#!/usr/bin/env python3
"""TASK31 gate 1 driver (task31_grid.py): the decisions over cells, and the
`identity` and `identity-replay` commands with the runner stood in for."""
import contextlib
import copy
import io
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import acceptance as a
import task31_cases as c
import task31_grid as g
import timing_grid as tg

BASE, CAND = a.BASE, "c" * 40
DIGEST = "d" * 64


def row(case, size, status="identical", differences=(), digest=DIGEST,
        files=("src/simp/src/Cond_rewr.sml",)):
    return dict(
        case=case, size=size, name=g.name_of(case, size), status=status,
        closure_differences=list(differences), work_differences=[],
        closure={s: dict(digest=digest, private=1, shared=1, heap=1)
                 for s in g.idt.SIDES},
        work={}, repo_files={s: sorted(files) for s in g.idt.SIDES})


def inventory(rows, expected=None, diagnostic=False, extra=()):
    names = expected if expected is not None else \
        [g.name_of(*k) for k in g.every()]
    return dict(
        schema=g.SCHEMA, baseline=BASE, candidate=CAND, expected=names,
        diagnostic=diagnostic, sources={
            p: dict(baseline="b", candidate="b") for p in c.SOURCES},
        runs=[dict(case=r["case"], size=r["size"], row=r) for r in rows])


def everything(**tweak):
    """Rows of every feasible cell."""
    return [tweak.get(g.name_of(*k)) or row(*k) for k in g.every()
            if g.name_of(*k) not in c.INFEASIBLE]


class Decide(unittest.TestCase):
    def test_every_cell_identical_is_an_identical_grid(self):
        d = g.decide(inventory(everything()))
        self.assertEqual(d["status"], "identical")
        self.assertEqual(d["counts"], dict(identical=278, different=0,
                                           unresolved=0))
        self.assertEqual(g.status_code(d), 0)
        self.assertEqual(len(d["cells"]), 278)

    def test_an_infeasible_cell_takes_the_identity_of_its_anchor(self):
        d = g.decide(inventory(everything()))
        found = d["cells"]["tactic_full_complete-10000"]
        self.assertEqual(found["status"], "identical")
        self.assertIn("derived from tactic_full_complete-0",
                      found["route"])
        self.assertEqual(found["work"], "not run: infeasible")
        self.assertEqual(found["survey"]["setup10000"],
                         c.INFEASIBLE_COST[
                             "tactic_full_complete-10000"][4])

    def test_a_different_anchor_makes_its_infeasible_cell_different(self):
        bad = row("tactic_full_complete", 0, "different",
                  [dict(kind="source", name="private/Cond_rewr.sml")])
        d = g.decide(inventory(everything(**{bad["name"]: bad})))
        self.assertEqual(d["cells"]["tactic_full_complete-10000"]["status"],
                         "different")
        self.assertEqual(d["status"], "different")
        self.assertEqual(g.status_code(d), 1)

    def test_a_closure_that_depends_on_the_cell_leaves_infeasible_open(self):
        odd = row("tactic_asm_complete", 10, digest="e" * 64)
        d = g.decide(inventory(everything(**{odd["name"]: odd})))
        self.assertFalse(d["closure_invariant"])
        self.assertEqual(d["cells"]["tactic_full_complete-10000"]["status"],
                         "unresolved")
        self.assertEqual(d["status"], "inconclusive")
        self.assertEqual(g.status_code(d), 2)

    def test_a_missing_cell_is_unresolved(self):
        rows = everything()[1:]
        d = g.decide(inventory(rows))
        self.assertEqual(d["counts"]["unresolved"], 1)
        self.assertEqual(g.status_code(d), 2)

    def test_a_missing_anchor_leaves_the_infeasible_cell_unresolved(self):
        rows = [r for r in everything()
                if r["name"] != "tactic_full_complete-0"]
        d = g.decide(inventory(rows))
        self.assertEqual(d["cells"]["tactic_full_complete-10000"]["status"],
                         "unresolved")

    def test_a_file_the_baseline_elaborates_outside_the_sources(self):
        r = row("traversal_construct", 0, files=("src/new/Unlisted.sml",))
        d = g.decide(inventory(everything(**{r["name"]: r})))
        self.assertEqual(d["uncovered"], ["src/new/Unlisted.sml"])
        self.assertEqual(g.status_code(d), 2)

    def test_a_file_only_the_candidate_elaborates_is_published(self):
        r = row("traversal_construct", 0)
        r["repo_files"]["candidate"] = ["src/simp/src/SimpTracking.sml"]
        d = g.decide(inventory(everything(**{r["name"]: r})))
        self.assertEqual(d["candidate_only"],
                         ["src/simp/src/SimpTracking.sml"])
        self.assertEqual(g.status_code(d), 0)

    def test_the_git_blobs_that_differ_are_published(self):
        inv = inventory(everything())
        inv["sources"][c.SOURCES[3]]["candidate"] = "other"
        self.assertEqual(g.decide(inv)["git_differing"], [c.SOURCES[3]])

    def test_a_diagnostic_decides_only_the_cells_it_names(self):
        names = ["traversal_construct-0"]
        d = g.decide(inventory([row("traversal_construct", 0)], names, True))
        self.assertEqual(d["status"], "identical")
        self.assertTrue(d["diagnostic"])
        self.assertEqual(list(d["cells"]), names)

    def test_the_report_names_the_files_that_differ(self):
        bad = row("traversal_construct", 0, "different", [
            dict(kind="source", name="private/Cond_rewr.sml"),
            dict(kind="product", name="private/Cond_rewr.sml X.uo")])
        d = g.decide(inventory(everything(**{bad["name"]: bad})))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            g.report(d)
        self.assertIn("traversal_construct-0: different", out.getvalue())
        self.assertIn("private/Cond_rewr.sml", out.getvalue())


class Commands(unittest.TestCase):
    """`identity` and `identity-replay` with the runner replaced: a fake
    run makes a folder whose bytes are the cell, and `idt.cell` is a
    function of the folder, so that the replay finds what the run found."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="task31-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.status = {}
        self.repo = self.root / "repo"
        self.repo.mkdir()

        def run_one(command, log, fds, timeout):
            folder = Path(command[command.index("--output") + 1])
            folder.mkdir()
            case = command[command.index("--performance-case") + 1]
            size = command[command.index("--performance-size") + 1]
            (folder / "cell").write_text("%s %s\n" % (case, size))
            self.commands = getattr(self, "commands", []) + [command]
            Path(log).write_text("log\n")
            return dict(exit=0, timed_out=False)

        def cell(folder, case, size, baseline, candidate, samples=3):
            text = (Path(folder) / "cell").read_text()
            self.assertEqual(text, "%s %d\n" % (case, size))
            return row(case, size, self.status.get(
                g.name_of(case, size), "identical"))

        self.patches = [
            mock.patch.object(g, "run_one", run_one),
            mock.patch.object(g.idt, "cell", cell),
            mock.patch.object(g, "source_blobs", lambda r, b, cn: {
                p: dict(baseline="b", candidate="b") for p in c.SOURCES}),
            mock.patch.object(g.ENGINE.h, "locked", self.locked)]
        for patch in self.patches:
            patch.start()
            self.addCleanup(patch.stop)

    @contextlib.contextmanager
    def locked(self, repo):
        yield []

    def args(self, *only, **more):
        out = self.root / more.pop("out", "out")
        argv = ["identity", "--output", str(out), "--baseline", BASE,
                "--candidate", CAND, "--authorize-measurements",
                "--repo", str(self.repo)]
        for name in only:
            argv += ["--only", name]
        return argv, out

    def main(self, argv):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            return g.main(argv), out.getvalue()

    def test_a_diagnostic_run_is_archived_decided_and_replayed(self):
        argv, out = self.args("traversal_construct-0",
                              "tactic_asm_complete-10")
        code, text = self.main(argv)
        self.assertEqual(code, 0, text)
        self.assertTrue((out / "traversal_construct-0.json.xz").is_file())
        self.assertEqual(a.load(out / "decisions.json")["status"],
                         "identical")
        flags = self.commands[0]
        self.assertTrue(flags[1].endswith("task31_snapshot.py"))
        self.assertEqual(flags[flags.index("--performance-pairs") + 1], "1")
        self.assertEqual(flags[flags.index("--batch-seconds") + 1], "0.1")
        self.assertNotIn("--batch-iterations", flags)
        code, text = self.main(["identity-replay", "--output", str(out),
                                "--repo", str(self.repo)])
        self.assertEqual(code, 0, text)

    def test_a_different_cell_gives_status_1_and_replays_as_such(self):
        self.status["traversal_construct-0"] = "different"
        argv, out = self.args("traversal_construct-0")
        self.assertEqual(self.main(argv)[0], 1)
        self.assertEqual(self.main(["identity-replay", "--output",
                                    str(out), "--repo",
                                    str(self.repo)])[0], 1)

    def test_a_tampered_archive_decision_or_row_is_found_on_replay(self):
        argv, out = self.args("traversal_construct-0")
        self.main(argv)
        replay = ["identity-replay", "--output", str(out), "--repo",
                  str(self.repo)]
        decisions = a.load(out / "decisions.json")
        (out / "decisions.json").unlink()
        bad = copy.deepcopy(decisions)
        bad["cells"]["traversal_construct-0"]["status"] = "different"
        a.save(out / "decisions.json", bad)
        self.assertEqual(self.main(replay)[0], tg.REFUSED)
        inv = a.load(out / "inventory.json")
        (out / "inventory.json").unlink()
        inv["runs"][0]["row"]["status"] = "different"
        a.save(out / "inventory.json", inv)
        self.assertEqual(self.main(replay)[0], tg.REFUSED)

    def test_the_command_needs_authorization_and_exact_pins(self):
        argv, out = self.args("traversal_construct-0")
        argv.remove("--authorize-measurements")
        self.assertEqual(self.main(argv)[0], tg.REFUSED)
        argv, out = self.args("traversal_construct-0", out="o2")
        argv[argv.index("--candidate") + 1] = "develop"
        self.assertEqual(self.main(argv)[0], tg.REFUSED)

    def test_a_cell_the_table_does_not_have_is_refused(self):
        argv, _ = self.args("nonsense-1")
        self.assertEqual(self.main(argv)[0], tg.REFUSED)

    def test_a_failed_runner_leaves_no_row_and_no_archive_of_a_cell(self):
        def fail(command, log, fds, timeout):
            folder = Path(command[command.index("--output") + 1])
            folder.mkdir()
            Path(log).write_text("x")
            return dict(exit=1, timed_out=False)
        argv, out = self.args("traversal_construct-0")
        with mock.patch.object(g, "run_one", fail):
            self.assertEqual(self.main(argv)[0], tg.REFUSED)
        self.assertEqual(a.load(out / "inventory.json")["runs"], [])
        self.assertFalse((out / "traversal_construct-0.json.xz").exists())

    def test_resume_skips_the_cells_that_are_done(self):
        argv, out = self.args("traversal_construct-0")
        self.main(argv)
        self.commands = []
        argv, out = self.args("traversal_construct-0",
                              "traversal_complete-0")
        code, _ = self.main(argv + ["--resume"])
        self.assertEqual(code, tg.REFUSED)  # other settings: other cells
        argv, _ = self.args("traversal_construct-0")
        code, _ = self.main(argv + ["--resume"])
        self.assertEqual(code, 0)
        self.assertEqual(self.commands, [])


if __name__ == "__main__":
    unittest.main()
