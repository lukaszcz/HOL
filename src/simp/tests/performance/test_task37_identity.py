#!/usr/bin/env python3
"""TASK37 identity of the client, matrix and downstream cells
(task37_identity.py): the cell sets, the reviewed table they are judged by,
the parity of the records with task31_identity_grid's, the refusals, the
seals, the binding of task31_identity_grid's names and the parallel jobs,
with the runner stood in for (nothing is measured)."""
import argparse
import contextlib
import copy
import io
import json
from pathlib import Path
import re
import tempfile
import threading
import unittest
from unittest import mock

import acceptance as a
import import_closure as ic
import matrix_schema as ms
import task30_cases
import task31_cases
import task31_grid as timing
import task31_identity as idt
import task31_identity_grid as g
import task37_sources as lists
import task37_cases as c37
import task37_identity as m
import test_task31_attempts as t31a
import test_task31_identity_grid as t31
import timing_grid as tg

BASE, CAND = a.BASE, "c" * 40
FILES = ("src/simp/src/simpLib.sig", "src/simp/src/simpLib.sml")
SMALL = ("frag_create", "frag_named")


def small(**more):
    """A table of two cases (12 cells) whose cells elaborate FILES."""
    return {"matrix": m.Table("matrix", "task37-matrix-identity", SMALL,
                              FILES, **more),
            "client": m.tables()["client"],
            "downstream": m.tables()["downstream"]}


class Cells(unittest.TestCase):
    def test_the_client_has_the_task31_cells_and_its_infeasible_rule(self):
        t = m.tables()["client"]
        self.assertEqual(t.ledger, "task37-client-identity")
        self.assertEqual(len(t.names()), 278)
        self.assertEqual(t.names(), [g.name_of(*k) for k in g.every()])
        self.assertEqual(t.names(), list(c37.CLIENT_CELLS))
        self.assertEqual(len(t.infeasible), 33)
        self.assertEqual(t.infeasible, tuple(task31_cases.INFEASIBLE))
        self.assertEqual(t.sources, tuple(task31_cases.SOURCES))
        self.assertEqual(t.view().INFEASIBLE, task31_cases.INFEASIBLE)

    def test_the_matrix_has_every_case_at_every_size(self):
        t = m.tables()["matrix"]
        self.assertEqual(t.ledger, "task37-matrix-identity")
        self.assertEqual(len(t.cases), 51)
        self.assertEqual(len(t.cells()), 306)
        self.assertEqual(len(set(t.names())), 306)
        self.assertEqual(sum(1 for c in t.cases
                             if c in task30_cases.CASES), 24)
        self.assertEqual(sum(len(ms.SIZE_SETS["rules"])
                             for c in t.cases if c not in
                             task30_cases.CASES), 162)
        self.assertEqual(sum(len(ms.SIZE_SETS["rules"])
                             for c in t.cases if c in
                             task30_cases.CASES), 144)
        self.assertLessEqual(set(task30_cases.CASES) | {
            "frag_create", "compile_batch", "storage_graph"}, set(t.cases))
        for case, size in t.cells():
            self.assertEqual(ms.get_case(case, size), MATRIX)
        self.assertIn("exclude_dproc-10000", t.names())
        self.assertIn("frag_record-0", t.names())
        # Every case matrix.json gives the matrix fixture, no other.
        self.assertEqual(set(t.cases), {
            k for k, v in ms.EXPECTED_CASES.items()
            if v["fixture"] == MATRIX})
        self.assertEqual(t.names(), list(c37.MATRIX_CELLS))
        self.assertEqual(t.infeasible, ())

    def test_the_downstream_cells_are_the_eleven_of_the_client_fixture(self):
        t = m.tables()["downstream"]
        self.assertEqual(t.ledger, "task37-downstream-identity")
        self.assertEqual(len(t.cells()), 11)
        self.assertEqual(sorted(t.names()), sorted(
            ["downstream_arithmetic-%d" % n for n in (1, 10, 100, 1000,
                                                      10000)] +
            ["downstream_reduce-%d" % n for n in (1, 10, 100, 1000, 10000)]
            + ["downstream_boss-0"]))
        for case, size in t.cells():
            self.assertEqual(ms.get_case(case, size), CLIENT)
        self.assertEqual(t.names(), list(c37.DOWNSTREAM_CELLS))

    def test_the_sources_are_those_of_the_sources_module(self):
        found = m.tables()
        self.assertEqual(found["client"].sources, lists.CLIENT)
        self.assertEqual(found["matrix"].sources, lists.MATRIX)
        self.assertEqual(found["downstream"].sources, lists.DOWNSTREAM)
        # Not the boundary lists the timing tables pin.
        self.assertIsNot(found["matrix"].sources, c37.MATRIX_TIMING_SOURCES)
        # No duplicate definition of a cell set or a source list here.
        text = (a.HERE / "task37_identity.py").read_text()
        for name in ("MATRIX =", "DOWNSTREAM =", "CLIENT =", "INFEASIBLE =",
                     "SOURCES =", "def matrix_cases", "def downstream_cases"):
            self.assertNotIn(name, text)

    def test_the_tables_are_three_disjoint_cell_sets(self):
        found = {k: set(t.names()) for k, t in m.tables().items()}
        self.assertEqual(sorted(len(v) for v in found.values()),
                         [11, 278, 306])
        self.assertEqual(len(set().union(*found.values())), 278 + 306 + 11)
        self.assertEqual(sorted(t.ledger for t in m.tables().values()),
                         ["task37-client-identity",
                          "task37-downstream-identity",
                          "task37-matrix-identity"])

    def test_the_view_is_what_the_grid_reads_and_checks_its_cells(self):
        v = m.tables()["matrix"].view()
        self.assertEqual((v.INFEASIBLE, v.PROCESS_TIMEOUT),
                         ((), task31_cases.PROCESS_TIMEOUT))
        with self.assertRaises(ValueError):
            m.Table("x", "y", SMALL, infeasible=("nonsense-1",)).view()

    def test_the_names_the_grid_reads_are_restored(self):
        names = ("cases", "attribution", "ENGINE", "IDENTITY_TABLE",
                 "IDENTITY_CODE", "CODE_HISTORY", "report", "measure")
        before = [getattr(g, n) for n in names]
        with self.assertRaises(RuntimeError), m.bound(
                m.tables()["matrix"], m.Pool(2)):
            self.assertEqual(g.IDENTITY_TABLE, "task37-matrix-identity")
            self.assertEqual(len(g.every()), 306)
            raise RuntimeError("x")
        self.assertEqual(before, [getattr(g, n) for n in names])
        self.assertEqual(g.IDENTITY_TABLE, "task31-identity")
        for key, count in (("client", 278), ("downstream", 11)):
            with m.bound(m.tables()[key]):
                self.assertEqual(len(g.every()), count)
            self.assertEqual(len(g.every()), 278)


class Binding(unittest.TestCase):
    """The mechanism that binds task31_identity_grid's module names."""

    def test_a_failing_pool_close_still_restores_the_names(self):
        class Broken(m.Pool):
            def close(self):
                raise OSError("close")
        before = g.IDENTITY_TABLE
        with self.assertRaises(OSError), m.bound(
                m.tables()["matrix"], Broken(2)):
            pass
        self.assertEqual(g.IDENTITY_TABLE, before)
        # And the binding is released: another can follow.
        with m.bound(m.tables()["downstream"]):
            self.assertEqual(g.IDENTITY_TABLE, "task37-downstream-identity")

    def test_a_failure_while_binding_restores_and_releases(self):
        table = m.tables()["matrix"]
        with mock.patch.object(table, "view", side_effect=ValueError("v")):
            with self.assertRaises(ValueError), m.bound(table):
                self.fail("not reached")
        self.assertEqual(g.IDENTITY_TABLE, "task31-identity")
        with m.bound(table):
            self.assertEqual(g.IDENTITY_TABLE, "task37-matrix-identity")

    def test_a_nested_binding_is_refused_and_leaves_the_first(self):
        with m.bound(m.tables()["matrix"]):
            with self.assertRaises(ValueError), m.bound(
                    m.tables()["downstream"]):
                self.fail("not reached")
            self.assertEqual(g.IDENTITY_TABLE, "task37-matrix-identity")
        self.assertEqual(g.IDENTITY_TABLE, "task31-identity")

    def test_a_binding_from_another_thread_is_refused(self):
        found = []

        def other():
            try:
                with m.bound(m.tables()["downstream"]):
                    found.append("bound")
            except ValueError as error:
                found.append(str(error))
        with m.bound(m.tables()["matrix"]):
            thread = threading.Thread(target=other)
            thread.start()
            thread.join()
            self.assertEqual(g.IDENTITY_TABLE, "task37-matrix-identity")
        self.assertEqual(len(found), 1)
        self.assertIn("already bound", found[0])
        self.assertEqual(g.IDENTITY_TABLE, "task31-identity")

    def test_the_reviewed_table_is_task37s(self):
        document = m.attribution(types_namespace(None), False)
        self.assertEqual(document["seal"], a.seal(c37.REVIEWED_FILE))
        self.assertNotEqual(c37.REVIEWED_FILE.name,
                            "task31_attributed.json")
        with m.bound(m.tables()["matrix"]):
            self.assertEqual(g.attribution(types_namespace(None), False)[
                "seal"], a.seal(c37.REVIEWED_FILE))
        # Outside a binding the client grid is still judged by its own.
        self.assertEqual(g.attribution(types_namespace(None), False)[
            "seal"], a.seal(g.attr.FILE))

    def test_another_table_is_a_diagnostic_only(self):
        other = a.HERE / "task31_attributed.json"
        self.assertEqual(m.attribution(types_namespace(other), True)[
            "seal"], a.seal(other))
        with self.assertRaises(ValueError) as caught:
            m.attribution(types_namespace(other), False)
        self.assertIn("task37_attributed.json", str(caught.exception))


def types_namespace(attributed):
    import argparse
    return argparse.Namespace(attributed=attributed)


MATRIX, CLIENT = "MatrixPerformance.sml", "ClientPerformance.sml"


class Code(unittest.TestCase):
    def test_the_modules_this_one_imports_are_sealed(self):
        text = (a.HERE / m.THIS).read_text()
        local = {n + ".py" for n in re.findall(
            r"^import (\w+)", text, re.M) if (a.HERE / (n + ".py")).is_file()}
        self.assertLessEqual(local - {"task31_identity.py"},
                             set(m.IDENTITY_CODE))
        self.assertIn("task31_identity.py", g.IDENTITY_CODE)
        self.assertIn(m.THIS, m.IDENTITY_CODE)
        self.assertIn("task37_cases.py", m.IDENTITY_CODE)
        self.assertEqual(set(g.IDENTITY_CODE) | set(m.EXTRA_CODE),
                         set(m.IDENTITY_CODE))
        self.assertEqual(set(m.EXTRA_CODE), {
            m.THIS, "task37_cases.py", "task37_sources.py",
            "task30_cases.py"})

    def test_the_recorded_seals_are_checked(self):
        with m.bound(m.tables()["matrix"]):
            now = g.code_seals()
            self.assertIn(m.THIS, now)
            g.check_code(now)
            bad = dict(now, **{m.THIS: {"sha256": "0"}})
            with self.assertRaises(ValueError):
                g.check_code(bad)
            with mock.patch.dict(m.CODE_HISTORY, {
                    m.THIS: [{"sha256": "0"}]}):
                g.check_code(bad)
            # A grid of the client's module has no seal of this one.
            old = {k: v for k, v in now.items() if k != m.THIS}
            with self.assertRaises(ValueError):
                g.check_code(old)


class Placement(unittest.TestCase):
    """The evidence of each table is its own, never TASK31's (the real
    engine, `Placed`, not the patched stand-in of `Commands`)."""

    REPO = Path("/clone")

    def test_each_table_has_its_own_ledger_stamp_and_log(self):
        seen = set()
        for key, t in m.tables().items():
            engine = m.engine_of(t)
            here = self.REPO / ".agent-files" / "evidence" / t.ledger
            self.assertEqual(engine.ledger_path(self.REPO),
                             here / "attempts.jsonl")
            self.assertEqual(engine.stamp_path(self.REPO),
                             here / "build-stamp.json")
            self.assertEqual(engine.prepare_log_path(self.REPO),
                             here / "prepare.log")
            seen |= {engine.ledger_path(self.REPO),
                     engine.stamp_path(self.REPO),
                     engine.prepare_log_path(self.REPO)}
        self.assertEqual(len(seen), 9)

    def test_task31s_paths_are_not_used(self):
        theirs = {timing.ENGINE.ledger_path(self.REPO),
                  timing.ENGINE.stamp_path(self.REPO),
                  timing.ENGINE.prepare_log_path(self.REPO)}
        self.assertEqual(theirs, {
            self.REPO / ".agent-files/evidence/task31/attempts.jsonl",
            self.REPO / ".agent-files/evidence/task31/build-stamp.json",
            self.REPO / ".agent-files/evidence/task31/prepare.log"})
        for t in m.tables().values():
            engine = m.engine_of(t)
            for path in (engine.ledger_path(self.REPO),
                         engine.stamp_path(self.REPO),
                         engine.prepare_log_path(self.REPO)):
                self.assertNotIn(path, theirs)
                self.assertNotIn("/task31/", str(path))
            # The engine is TASK31's table, under this table's name.
            self.assertEqual(engine.t.name, t.ledger)
            self.assertEqual(engine.t.family, t.ledger)
            self.assertEqual(engine.t.sealed, timing.TABLE.sealed)
        self.assertEqual(timing.TABLE.name, "task31")

    def test_the_command_binds_its_engine_and_restores_task31s(self):
        before = g.ENGINE
        for t in m.tables().values():
            with m.bound(t):
                self.assertIsNot(g.ENGINE, before)
                self.assertEqual(
                    g.ENGINE.h.ledger_path(self.REPO),
                    self.REPO / ".agent-files/evidence" / t.ledger /
                    "attempts.jsonl")
            self.assertIs(g.ENGINE, before)

    def test_prepare_stamps_the_tables_own_place(self):
        seen = []

        def prepare(engine, args):
            seen.append((engine.stamp_path(args.repo), g.ENGINE is engine))
            return 0
        with mock.patch.object(m.Placed, "prepare", prepare):
            code = m.main(["prepare", "--table", "matrix", "--repo",
                           str(self.REPO)])
        self.assertEqual(code, 0)
        self.assertEqual(seen, [(self.REPO / ".agent-files/evidence/"
                                 "task37-matrix-identity/"
                                 "build-stamp.json", True)])
        self.assertIs(g.ENGINE, timing.ENGINE)

    def test_prepare_needs_a_table(self):
        with contextlib.redirect_stderr(io.StringIO()), \
                self.assertRaises(SystemExit):
            m.main(["prepare"])


class Closure(unittest.TestCase):
    """The carried-over invariant of test_task31_attempts.Modules for this
    module: every local module it imports, to the transitive closure, is
    in IDENTITY_CODE or reached only by an exempt import edge with a
    stated reason."""

    TIMING_SAMPLES = (
        "task37_cases.py imports it for the timing samples (the sample "
        "of the client table: its follow-up cells) and no identity cell "
        "or source list derives from it: the identity cells are the "
        "cases, and the lists are task37_sources.py's")
    D4_LISTS = (
        "task37_cases.py imports it for the D4 list of TASK29A (the "
        "disposition's and the timing sample's), not read by any identity "
        "cell or decision")

    @classmethod
    def exempt(cls):
        found = t31a.Modules.runtime_edges(
            "loading", "path_schema", "prepare_patch", "check_patch")
        found.update(t31a.Modules.edges(
            t31a.Modules.TASK30_IDENTITY,
            ("task31_grid", "task30_grid", None)))
        found.update(t31a.Modules.edges(
            cls.TIMING_SAMPLES, ("task37_cases", "task31_followup", None)))
        found.update(t31a.Modules.edges(
            cls.D4_LISTS, ("task37_cases", "task29a_grid", None)))
        return found

    ROOTS = t31a.Modules.IDENTITY_ROOTS + ("task37_identity",)

    def covered(self, sources, exempt):
        stems = {Path(n).stem for n in m.IDENTITY_CODE}
        found, used = ic.closure(sources, self.ROOTS, exempt)
        return found - stems, set(exempt) - used, [
            e for e in exempt if e[1] in stems]

    def test_the_identity_module_imports_only_sealed_code(self):
        unsealed, unused, redundant = self.covered(ic.sources(),
                                                   self.exempt())
        self.assertEqual(sorted(unsealed), [])
        self.assertEqual(sorted(unused, key=str), [])
        self.assertEqual(redundant, [])
        for edge, reason in self.exempt().items():
            self.assertTrue(reason, edge)

    def test_the_cell_set_modules_are_sealed(self):
        stems = {Path(n).stem for n in m.IDENTITY_CODE}
        for name in ("task37_cases", "task37_sources", "task30_cases",
                     "task37_identity"):
            self.assertIn(name, stems)
        self.assertNotIn("task29a_grid", stems)
        self.assertNotIn("task31_followup", stems)

    def test_a_new_import_is_found(self):
        sources = ic.sources()
        sources["task37_cases"] += "\nimport allocation_boundary\n"
        unsealed, _, _ = self.covered(sources, self.exempt())
        self.assertIn("allocation_boundary", unsealed)
        sources = ic.sources()
        sources["task37_identity"] += "\nimport task29a_grid\n"
        unsealed, _, _ = self.covered(sources, self.exempt())
        self.assertIn("task29a_grid", unsealed)


class Commands(t31.Commands):
    """The commands of this module over the fake runner of the TASK31
    tests, which `setUp` already installs on task31_identity_grid (the
    functions this module runs)."""

    def setUp(self):
        super().setUp()
        self.broken = set()
        self.scratch = self.root / "tmp"
        self.scratch.mkdir()
        patch = mock.patch.object(tempfile, "tempdir", str(self.scratch))
        patch.start()
        self.addCleanup(patch.stop)

        def run_one(command, log, fds, timeout):
            folder = Path(command[command.index("--output") + 1])
            folder.mkdir()
            case = command[command.index("--performance-case") + 1]
            size = command[command.index("--performance-size") + 1]
            with self.guard:
                self.commands = self.commands + [command]
            Path(log).write_text("log\n")
            if "%s-%s" % (case, size) in self.broken:
                return dict(exit=1, timed_out=False)
            (folder / "cell").write_text("%s %s\n" % (case, size))
            return dict(exit=0, timed_out=False)
        self.guard = threading.Lock()
        self.commands = []
        patch = mock.patch.object(g, "run_one", run_one)
        patch.start()
        self.addCleanup(patch.stop)
        self.tables = small()
        engine = g.ENGINE   # patched by the TASK31 setUp (`Placement` tests
        # the real, per-table engine)
        for patch in (
                mock.patch.object(m, "tables", lambda: self.tables),
                mock.patch.object(m, "engine_of", lambda table: engine),
                mock.patch.object(t31.c, "SOURCES", FILES)):
            patch.start()
            self.addCleanup(patch.stop)

    @staticmethod
    def blobs(repo, baseline, candidate, entries, tree):
        found = {p: dict(baseline="b", candidate="b") for p in FILES}
        found.update({e["path"]: dict(baseline=e["baseline_blob"],
                                      candidate=e["candidate_blob"])
                      for e in entries})
        return found

    def cell_row(self, folder, case, size, baseline, candidate,
                 samples=3, entries=()):

        return t31.row(case, size, entries=entries, files=FILES)

    def args(self, *only, table="matrix", jobs=1, **more):
        argv, out = super().args(*only, **more)
        return [argv[0], "--table", table, "--jobs", str(jobs)] + \
            argv[1:], out

    def main(self, argv):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            return m.main(argv), out.getvalue()

    def run_whole(self, **more):
        with self.whole_grid():
            argv, out = self.args(**more)
            code, text = self.main(argv)
        return code, text, out

    def replay(self, out, table="matrix", *more):
        with self.whole_grid():
            return self.replay_now(out, table, *more)

    def replay_now(self, out, table, *more):
        return self.main(["identity-replay", "--table", table, "--output",
                          str(out), "--repo", str(self.repo), *more])

    def start(self):
        patch = mock.patch.object(idt, "cell", self.cell_row)
        patch.start()
        self.addCleanup(patch.stop)

    def test_a_diagnostic_cell_is_run_archived_decided_and_replayed(self):
        self.start()
        argv, out = self.args("frag_create-0", "frag_named-10")
        code, text = self.main(argv)
        self.assertEqual(code, 0, text)
        self.assertIn("TASK37 matrix identity: attributed", text)
        self.assertTrue((out / "frag_create-0.json.xz").is_file())
        flags = self.commands[0]
        self.assertTrue(flags[1].endswith("task31_snapshot.py"))
        self.assertEqual(flags[flags.index("--performance-pairs") + 1], "1")
        self.assertEqual(flags[flags.index("--samples") + 1], "3")
        self.assertEqual(flags[flags.index("--batch-seconds") + 1], "1.0")
        self.assertEqual((g.ID_PAIRS, g.ID_SAMPLES, g.ID_SECONDS),
                         (1, 3, 1.0))
        code, text = self.replay(out)
        self.assertEqual(code, 0, text)

    def test_the_whole_table_is_bound_to_the_checkout_and_replayed(self):
        self.start()
        code, text, out = self.run_whole()
        self.assertEqual(code, 0, text)
        decisions = a.load(out / "decisions.json")
        self.assertEqual(sum(decisions["counts"].values()), 12)
        self.assertEqual(decisions["counts"]["unresolved"], 0)
        self.assertEqual(len(self.commands), 12)
        self.assertEqual(self.replay(out)[0], 0)

    def test_the_records_have_the_keys_of_the_client_grid(self):
        self.start()
        argv, mine = self.args("frag_create-0", out="matrix")
        self.assertEqual(self.main(argv)[0], 0)
        ledger = self.root / "attempts.jsonl"
        # The client grid, run by its own module with the same stand-ins.
        out = io.StringIO()
        client = self.root / "client"
        with contextlib.redirect_stdout(out):
            code = g.main(["identity", "--output", str(client),
                           "--baseline", BASE, "--candidate", CAND,
                           "--authorize-measurements", "--repo",
                           str(self.repo), "--only",
                           "traversal_construct-0"])
        self.assertEqual(code, 0, out.getvalue())
        one, two = (a.load(d / "inventory.json") for d in (client, mine))
        self.assertEqual(sorted(one), sorted(two))
        self.assertEqual(one["schema"], two["schema"])
        self.assertEqual(
            sorted(one["code"] | dict.fromkeys(m.EXTRA_CODE, 0)),
            sorted(two["code"]))
        self.assertEqual(sorted(one["runs"][0]), sorted(two["runs"][0]))
        self.assertEqual(sorted(one["runs"][0]["row"]),
                         sorted(two["runs"][0]["row"]))
        for key in ("attributed", "source_tree", "sources"):
            self.assertEqual(sorted(one[key]), sorted(two[key]), key)
        d1, d2 = (a.load(d / "decisions.json") for d in (client, mine))
        self.assertEqual(sorted(d1), sorted(d2))
        self.assertEqual(d1["schema"], d2["schema"])
        self.assertEqual(sorted(d1["counts"]), sorted(d2["counts"]))
        self.assertEqual(sorted(d1["cells"]["traversal_construct-0"]),
                         sorted(d2["cells"]["frag_create-0"]))
        # The ledger tells the tables apart and holds the same fields.
        lines = [json.loads(x) for x in ledger.read_text().splitlines()]
        tables = [x["table"] for x in lines]
        self.assertEqual(tables, ["task37-matrix-identity"] * 2 +
                         ["task31-identity"] * 2)
        self.assertEqual(sorted(lines[0]), sorted(lines[2]))
        self.assertEqual(sorted(lines[1]), sorted(lines[3]))
        self.assertEqual(m.attempt_counts(self.tables["matrix"], ledger,
                                          CAND), (1, 1))
        self.assertEqual(g.attempt_counts(ledger, CAND), (1, 1))

    def refusal(self, argv, why):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            code, text = self.main(argv)
        self.assertEqual(code, tg.REFUSED, text)
        self.assertIn(why, err.getvalue())

    def test_the_refusals(self):
        self.start()
        argv, out = self.args("frag_create-0")
        bare = list(argv)
        bare.remove("--authorize-measurements")
        self.refusal(bare, "measurement authorization required")
        argv[argv.index("--candidate") + 1] = "develop"
        self.refusal(argv, "")
        argv, _ = self.args("nonsense-1")
        self.refusal(argv, "unknown or repeated cell")
        argv, _ = self.args("frag_create-0", "frag_create-0")
        self.refusal(argv, "unknown or repeated cell")
        # A cell of the other table is unknown to this one.
        argv, _ = self.args("downstream_boss-0")
        self.refusal(argv, "unknown or repeated cell")
        argv, _ = self.args("frag_create-0", jobs=0)
        self.refusal(argv, "--jobs")
        # A full grid of a table whose sources are not derived yet.
        self.tables = {k: m.Table(k, t.ledger, t.cases)
                       for k, t in self.tables.items()}
        argv, out = self.args()
        self.refusal(argv, "has no sources yet")
        self.assertFalse(out.exists())
        # A diagnostic of it is allowed: that is how they are derived.
        argv, out = self.args("frag_create-0")
        self.assertEqual(self.main(argv)[0], 2)
        self.assertEqual(self.main(["sources", "--output", str(out)])[1]
                         .split(), sorted(FILES))
        err = io.StringIO()
        with contextlib.redirect_stderr(err), \
                self.assertRaises(SystemExit) as caught:
            self.main(["identity", "--table", "other"])
        self.assertEqual(caught.exception.code, 2)

    def test_a_full_grid_is_judged_by_the_task37_reviewed_table(self):
        self.start()
        seen = []
        with mock.patch.object(g, "prepare_table", lambda args, doc: (
                seen.append(doc))):
            code, text, out = self.run_whole()
        self.assertEqual(code, 0, text)
        self.assertEqual(len(seen), 1)
        self.assertEqual(seen[0]["seal"], a.seal(c37.REVIEWED_FILE))
        found = a.load(out / "inventory.json")["attributed"]
        self.assertEqual(found["file"], a.seal(c37.REVIEWED_FILE))
        self.assertEqual(found["table"], seen[0]["entries"])
        self.assertNotEqual(found["file"], a.seal(g.attr.FILE))
        # The reviewed table of a diagnostic may be another; of a full grid
        # it may not.
        argv, _ = self.args(out="other")
        argv += ["--attributed", str(a.HERE / "task31_attributed.json")]
        self.refusal(argv, "task37_attributed.json")
        self.assertFalse((self.root / "other").exists())

    def test_the_client_table_derives_its_infeasible_cells(self):
        self.start()
        heavy = c37.INFEASIBLE[0]
        case, _ = c37.split(heavy)
        self.tables = small()
        self.tables["client"] = m.Table(
            "client", "task37-client-identity", (case,), FILES,
            (heavy,))
        sizes = c37.sizes(case)
        argv, out = self.args(table="client")
        with self.whole_grid():
            code, text = self.main(argv)
        self.assertEqual(code, 0, text)
        ran = {c[c.index("--performance-size") + 1] for c in self.commands}
        self.assertEqual(ran, {str(n) for n in sizes if n != 10000})
        found = a.load(out / "decisions.json")["cells"][heavy]
        self.assertIn("derived from", found["route"])
        self.assertEqual(found["status"], "identical")
        lines = [json.loads(x) for x in (self.root / "attempts.jsonl")
                 .read_text().splitlines()]
        self.assertEqual({x["table"] for x in lines},
                         {"task37-client-identity"})
        with self.whole_grid():
            self.assertEqual(self.replay_now(out, "client")[0], 0)

    def test_the_refusal_of_a_table_without_sources_says_how_to_get_them(
            self):
        self.start()
        self.tables = {k: m.Table(k, t.ledger, t.cases, constant=k.upper())
                       for k, t in self.tables.items()}
        argv, out = self.args(table="downstream")
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            self.assertEqual(self.main(argv)[0], tg.REFUSED)
        text = err.getvalue()
        for part in ("no sources yet", "--only", "sources --output DIR",
                     "task37_sources.DOWNSTREAM"):
            self.assertIn(part, text)

    def test_the_wrong_table_or_a_foreign_grid_is_not_replayed(self):
        self.start()
        argv, out = self.args("frag_create-0")
        self.assertEqual(self.main(argv)[0], 0)
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            code = self.main(["identity-replay", "--table", "downstream",
                              "--output", str(out), "--repo",
                              str(self.repo)])[0]
        self.assertEqual(code, tg.REFUSED)
        # A grid the client module made has no seal of this module's.
        client = self.root / "client"
        with contextlib.redirect_stdout(io.StringIO()):
            g.main(["identity", "--output", str(client), "--baseline",
                    BASE, "--candidate", CAND, "--authorize-measurements",
                    "--repo", str(self.repo), "--only",
                    "traversal_construct-0"])
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            code = self.replay(client)[0]
        self.assertEqual(code, tg.REFUSED)
        self.assertIn("identity code recorded", err.getvalue())

    def test_a_changed_seal_is_refused_on_replay_and_history_admits_it(self):
        self.start()
        argv, out = self.args("frag_create-0")
        self.assertEqual(self.main(argv)[0], 0)
        inv = a.load(out / "inventory.json")
        (out / "inventory.json").unlink()
        inv["code"][m.THIS] = {"sha256": "0"}
        a.save(out / "inventory.json", inv)
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            self.assertEqual(self.replay(out)[0], tg.REFUSED)
        self.assertIn(m.THIS, err.getvalue())
        with mock.patch.dict(m.CODE_HISTORY, {m.THIS: [{"sha256": "0"}]}):
            self.assertEqual(self.replay(out)[0], 0)

    def test_a_different_cell_gives_status_1_and_replays_as_such(self):
        def cell(folder, case, size, baseline, candidate, samples=3,
                 entries=()):
            return t31.row(case, size, "different" if case == "frag_create"
                           else "identical", entries=entries, files=FILES)
        argv, out = self.args("frag_create-0")
        with mock.patch.object(idt, "cell", cell):
            self.assertEqual(self.main(argv)[0], 1)
            self.assertEqual(self.replay(out)[0], 1)

    # Parallel jobs

    def records(self, out):
        """Everything a grid recorded, but what a run makes new."""
        inv = a.load(out / "inventory.json")
        for key in ("attempt", "checkout"):
            inv.pop(key, None)
        archives = {p.name: a.seal(p) for p in sorted(out.glob("*.xz"))}
        return inv, a.load(out / "decisions.json"), archives

    def ledger_events(self):
        ledger = self.root / "attempts.jsonl"
        return [(x["event"], x.get("status")) for x in
                (json.loads(t) for t in ledger.read_text().splitlines())]

    def test_jobs_give_the_records_of_one_job(self):
        self.start()
        code, text, one = self.run_whole(out="one")
        self.assertEqual(code, 0, text)
        order = [c[c.index("--performance-case") + 1] + "-" +
                 c[c.index("--performance-size") + 1]
                 for c in self.commands]
        self.commands = []
        code, text, three = self.run_whole(out="three", jobs=3)
        self.assertEqual(code, 0, text)
        self.assertEqual(sorted(c[c.index("--performance-case") + 1] + "-" +
                                c[c.index("--performance-size") + 1]
                                for c in self.commands), sorted(order))
        a1, a3 = self.records(one), self.records(three)
        self.assertEqual(a1[0]["runs"], a3[0]["runs"])
        self.assertEqual([r["archive"] for r in a3[0]["runs"]],
                         [n + ".json.xz" for n in self.tables["matrix"]
                          .names()])
        self.assertEqual(a1, a3)
        ends = [x for x in text.splitlines() if x.startswith("END")]
        self.assertEqual([x.split()[1] for x in ends],
                         self.tables["matrix"].names())
        self.assertEqual(self.ledger_events(), [("open", None),
                         ("close", "attributed")] * 2)
        self.assertEqual(list(self.scratch.iterdir()), [])
        self.assertEqual(self.replay(three)[0], 0)

    def test_the_jobs_do_run_at_once(self):
        """The first three cells wait for each other: only a run that
        has three jobs at once gets past (else the barrier times out and
        the cell fails)."""
        self.start()
        hold, calls = threading.Barrier(3, timeout=20), []
        ordinary = g.run_one

        def waiting(*args):
            calls.append(1)
            if len(calls) <= 3:
                hold.wait()
            return ordinary(*args)
        with mock.patch.object(g, "run_one", waiting):
            code, text, out = self.run_whole(jobs=3)
        self.assertEqual(code, 0, text)

    def test_a_failed_job_is_recorded_and_the_run_stops_cleanly(self):
        self.start()
        names = self.tables["matrix"].names()
        self.broken = {names[5]}
        code, text, out = self.run_whole(jobs=3)
        self.assertEqual(code, tg.REFUSED, text)
        inv = a.load(out / "inventory.json")
        self.assertEqual([r["archive"] for r in inv["runs"]],
                         [n + ".json.xz" for n in names[:5]])
        self.assertFalse((out / (names[5] + ".json.xz")).exists())
        self.assertEqual(self.ledger_events(),
                         [("open", None), ("close", "interrupted")])
        self.assertEqual(list(self.scratch.iterdir()), [])
        self.assertEqual([t.name for t in threading.enumerate()
                          if t.name.startswith("identity")], [])
        self.assertLess(len(self.commands), len(names))
        # The resume measures the cells that are missing, with the
        # records of an uninterrupted run.
        self.broken = set()
        with self.whole_grid():
            argv, out = self.args(jobs=2)
            code, text = self.main(argv + ["--resume"])
        self.assertEqual(code, 0, text)
        self.commands = []
        _, _, clean = self.run_whole(out="clean")
        a1, a2 = self.records(clean), self.records(out)
        self.assertEqual(a1[0]["runs"], a2[0]["runs"])
        self.assertEqual(a1[1:], a2[1:])
        self.assertEqual(self.replay(out)[0], 0)

    def test_a_failed_job_leaves_its_archive_set_aside(self):
        self.start()
        name = "frag_named-10"

        def refuse(folder, case, size, baseline, candidate, samples=3,
                   entries=()):
            if g.name_of(case, size) == name:
                raise ValueError("the row is refused")
            return t31.row(case, size, entries=entries, files=FILES)
        argv, out = self.args(jobs=2)
        with self.whole_grid(), mock.patch.object(idt, "cell", refuse):
            self.assertEqual(self.main(argv)[0], tg.REFUSED)
        self.assertTrue((out / (name + ".json.xz.failed-1")).is_file())
        self.assertFalse((out / (name + ".json.xz")).exists())
        self.assertEqual(list(self.scratch.iterdir()), [])

    def test_an_infeasible_cell_derives_from_its_case_with_jobs(self):
        self.start()
        self.tables = small(infeasible=("frag_create-10000",))
        code, text, out = self.run_whole(jobs=4)
        self.assertEqual(code, 0, text)
        flags = [c[c.index("--performance-size") + 1] + c[
            c.index("--performance-case") + 1] for c in self.commands]
        self.assertNotIn("10000frag_create", flags)
        self.assertIn("10000frag_named", flags)
        found = a.load(out / "decisions.json")["cells"][
            "frag_create-10000"]
        self.assertIn("derived from frag_create-0", found["route"])
        self.assertEqual(found["status"], "identical")
        self.assertEqual(self.replay(out)[0], 0)

    def test_a_missing_anchor_leaves_the_derived_cell_unresolved(self):
        """A diagnostic of the infeasible cell alone measures no anchor:
        the derived cell is `unresolved`, and the grid not conclusive."""
        self.start()
        self.tables = small(infeasible=("frag_create-10000",))
        argv, out = self.args("frag_create-10000", jobs=2)
        code, text = self.main(argv)
        self.assertEqual(code, 2, text)
        found = a.load(out / "decisions.json")
        row = found["cells"]["frag_create-10000"]
        self.assertEqual(row["status"], "unresolved")
        self.assertEqual(found["counts"]["unresolved"], 1)
        self.assertEqual(found["status"], "inconclusive")
        self.assertEqual(self.commands, [])

    def test_a_broken_anchor_refuses_the_grid(self):
        self.start()
        self.tables = small(infeasible=("frag_create-10000",))
        self.broken = {"frag_create-0"}
        code, _, _ = self.run_whole(jobs=4)
        self.assertEqual(code, tg.REFUSED)

    def args_for(self, repo=None):
        return argparse.Namespace(
            repo=repo or self.repo, baseline=BASE, candidate=CAND,
            timeout=5)

    def test_a_later_failure_does_not_skip_an_earlier_cell(self):
        """The race of a job that checks `stop` at entry: cell 1 fails,
        and cell 0 (earlier in the grid's order, not yet started) must
        still run, so that the failure is what the parent meets."""
        self.start()
        names = self.tables["matrix"].names()[:3]
        self.broken = {names[1]}
        inventory = dict(attributed=dict(table=[]), diagnostic=True)
        pool = m.Pool(2)
        pool.order = {n: i for i, n in enumerate(names)}
        with m.bound(self.tables["matrix"], pool):
            failure = pool.job(self.args_for(), names[1], inventory, [])
            self.assertIsInstance(failure, m.Failure)
            self.assertIsInstance(failure.error, ValueError)
            earlier = pool.job(self.args_for(), names[0], inventory, [])
            self.assertIsInstance(earlier, dict)
            self.assertEqual(earlier["row"]["case"], "frag_create")
            # Only the cells after the failed one are skipped.
            self.assertIsNone(pool.job(self.args_for(), names[2],
                                       inventory, []))
            self.assertEqual(pool.failed, 1)
            # An earlier failure takes over, a later one does not.
            self.broken = {names[0]}
            second = pool.job(self.args_for(), names[0], inventory, [])
            self.assertIsInstance(second, m.Failure)
            self.assertEqual(pool.failed, 0)

    def test_the_real_error_is_raised_with_its_archive_set_aside(self):
        self.start()
        names = self.tables["matrix"].names()
        self.broken = {names[2]}
        argv, out = self.args(jobs=3)
        err = io.StringIO()
        with self.whole_grid(), contextlib.redirect_stderr(err):
            self.assertEqual(self.main(argv)[0], tg.REFUSED)
        self.assertIn("identity runner failed: " + names[2], err.getvalue())
        self.assertNotIn("skipped", err.getvalue())
        inv = a.load(out / "inventory.json")
        self.assertEqual([r["archive"] for r in inv["runs"]],
                         [n + ".json.xz" for n in names[:2]])
        self.assertTrue(
            (out / (names[2] + ".json.xz.failed-1")).is_file())
        self.assertEqual(list(self.scratch.iterdir()), [])

    def test_the_scratch_directories_are_named_apart_from_the_client(self):
        self.assertTrue(m.Pool(2).prefix.startswith("task37-"))
        self.assertNotEqual(m.Pool(2).prefix, "task31-identity-")
        with self.assertRaises(ValueError):
            m.Pool(0)


# The tests of the TASK31 class are about the client cells: this class
# inherits its fixtures only.
for _name in dir(t31.Commands):
    if _name.startswith("test_") and _name not in vars(Commands):
        setattr(Commands, _name, None)


if __name__ == "__main__":
    unittest.main()
