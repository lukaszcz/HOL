#!/usr/bin/env python3
"""TASK31 gate 1 (task31_identity_grid.py): the decisions over cells, and the
`identity` and `identity-replay` commands with the runner stood in for."""
import argparse
import contextlib
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import acceptance as a
import task31_attribution as attr
import task31_cases as c
import task31_grid as timing
import task31_identity_grid as g
import timing_grid as tg

BASE, CAND = a.BASE, "c" * 40
DIGEST = "d" * 64
ENTRIES = [dict(
    path="src/simp/src/Cond_rewr.sig", kind="source",
    baseline_blob="1" * 40, candidate_blob="2" * 40,
    reason="adds a spec", gate="gate 2")]
HEAP_ENTRY = dict(
    path="src/1/ThmAttribute.sml", kind="heap", baseline_blob="3" * 40,
    candidate_blob="4" * 40, reason="in the heap", gate="gate 5")


def row(case, size, status="identical", differences=(), digest=DIGEST,
        files=c.SOURCES, entries=ENTRIES,
        attributed=(), heap=()):
    return dict(
        case=case, size=size, name=g.name_of(case, size), status=status,
        closure_differences=list(differences), work_differences=[],
        attributed=list(attributed), attribution_table=g.attr.digest(entries),
        head=CAND, dirty=[], inputs={"i": 1}, tools={"t": 1},
        closure={s: dict(digest=digest, private=1, shared=1, heap=1)
                 for s in g.idt.SIDES},
        work={}, repo_files={s: sorted(files) for s in g.idt.SIDES},
        loaded_files={s: sorted(files) for s in g.idt.SIDES},
        heap_files={s: sorted(heap) for s in g.idt.SIDES})


def inventory(rows, expected=None, diagnostic=False, entries=ENTRIES,
              changed=None):
    """`changed` is {path: (baseline blob, candidate blob)} of files below
    src/ that differ besides the entries'."""
    names = expected if expected is not None else \
        [g.name_of(*k) for k in g.every()]
    blobs = {p: dict(baseline="b", candidate="b") for p in c.SOURCES}
    for e in entries:
        blobs[e["path"]] = dict(baseline=e["baseline_blob"],
                                candidate=e["candidate_blob"])
    for path, (old, new) in (changed or {}).items():
        blobs[path] = dict(baseline=old, candidate=new)
    return dict(
        schema=g.SCHEMA, baseline=BASE, candidate=CAND, expected=names,
        diagnostic=diagnostic, sources=blobs,
        attributed=dict(file={}, table=list(entries),
                        digest=g.attr.digest(entries)),
        runs=[dict(case=r["case"], size=r["size"], row=r) for r in rows])


def everything(entries=ENTRIES, **tweak):
    """Rows of every feasible cell."""
    return [tweak.get(g.name_of(*k)) or row(*k, entries=entries)
            for k in g.every() if g.name_of(*k) not in c.INFEASIBLE]


class Decide(unittest.TestCase):
    def test_every_cell_identical_is_an_identical_grid(self):
        inv = inventory(everything(entries=[]), entries=[])
        d = g.decide(inv)
        self.assertEqual(d["status"], "identical")
        self.assertEqual(d["counts"], dict(
            identical=278, attributed=0, different=0, unresolved=0))
        self.assertEqual(g.status_code(d), 0)
        self.assertEqual(len(d["cells"]), 278)

    def test_a_reviewed_file_makes_an_attributed_grid_that_passes(self):
        d = g.decide(inventory(everything()))
        self.assertEqual(d["status"], "attributed")
        self.assertEqual(d["attributed"], ["src/simp/src/Cond_rewr.sig"])
        self.assertEqual(g.status_code(d), 0)

    def test_an_attributed_cell_is_counted_and_passes(self):
        r = row("traversal_construct", 0, "attributed")
        d = g.decide(inventory(everything(**{r["name"]: r})))
        self.assertEqual((d["status"], d["counts"]["attributed"]),
                         ("attributed", 1))
        self.assertEqual(g.status_code(d), 0)

    def test_an_infeasible_cell_takes_the_worst_identity_of_its_case(self):
        d = g.decide(inventory(everything()))
        found = d["cells"]["tactic_full_complete-10000"]
        self.assertEqual(found["status"], "identical")
        self.assertIn("derived from tactic_full_complete-0",
                      found["route"])
        self.assertEqual(found["work"], "not run: infeasible")
        self.assertNotIn("survey", found)
        r = row("tactic_full_complete", 1, "attributed", attributed=[
            dict(path="src/simp/src/Cond_rewr.sig")])
        d = g.decide(inventory(everything(**{r["name"]: r})))
        found = d["cells"]["tactic_full_complete-10000"]
        self.assertEqual(found["status"], "attributed")
        self.assertEqual([x["path"] for x in found["attributed"]],
                         ["src/simp/src/Cond_rewr.sig"])

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
        r = row("traversal_construct", 0,
                files=c.SOURCES + ("src/new/Unlisted.sml",))
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
        inv = inventory(everything(entries=[]), entries=[])
        inv["sources"][c.SOURCES[3]]["candidate"] = "other"
        self.assertEqual(g.decide(inv)["git_differing"], [c.SOURCES[3]])

    def test_a_diagnostic_decides_only_the_cells_it_names(self):
        names = ["traversal_construct-0"]
        d = g.decide(inventory([row("traversal_construct", 0)], names, True))
        self.assertEqual(d["status"], "attributed")
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
        self.assertIn("ATTRIBUTED src/simp/src/Cond_rewr.sig",
                      out.getvalue())

    def test_a_cell_judged_by_another_table_is_refused(self):
        r = row("traversal_construct", 0, entries=[])
        with self.assertRaises(ValueError):
            g.decide(inventory(everything(**{r["name"]: r})))


class Tree(unittest.TestCase):
    """Every tracked file that differs is attributed, excluded for a
    reviewed reason, or shown unloaded."""

    def decide(self, changed, heap=(), entries=ENTRIES):
        rows = everything(entries, **{"traversal_construct-0": row(
            "traversal_construct", 0, heap=heap, entries=entries)})
        return g.decide(inventory(rows, changed=changed, entries=entries))

    def test_a_loaded_file_without_an_entry_is_different(self):
        d = self.decide({"src/simp/src/Cond_rewr.sml": ("5" * 40, "6" * 40)})
        self.assertEqual((d["status"], d["unaccounted"]),
                         ("different", ["src/simp/src/Cond_rewr.sml"]))
        self.assertEqual(g.status_code(d), 1)

    def test_a_file_of_the_heap_is_loaded_and_needs_an_entry(self):
        changed = {HEAP_ENTRY["path"]: ("3" * 40, "4" * 40)}
        d = self.decide(changed, heap=(HEAP_ENTRY["path"],))
        self.assertEqual(d["unaccounted"], [HEAP_ENTRY["path"]])
        d = self.decide(changed, heap=(HEAP_ENTRY["path"],),
                        entries=ENTRIES + [HEAP_ENTRY])
        self.assertEqual(d["unaccounted"], [])
        self.assertEqual(d["tree"][HEAP_ENTRY["path"]][0], "attributed")

    def test_a_file_no_receipt_loaded_is_unloaded_and_not_different(self):
        d = self.decide({"src/other/Zip.sml": ("5" * 40, "6" * 40)})
        self.assertEqual(d["tree"]["src/other/Zip.sml"][0], "unloaded")
        self.assertEqual(d["unaccounted"], [])
        self.assertEqual(d["status"], "attributed")

    def test_a_build_file_of_a_loaded_directory_needs_an_entry(self):
        path = "src/simp/src/Holmakefile"
        d = self.decide({path: ("5" * 40, "6" * 40)})
        self.assertEqual(d["tree"][path][0], "unattributed-build")
        self.assertEqual(d["unaccounted"], [path])
        self.assertEqual(d["build_files"], {path: "unattributed-build"})
        path = "src/other/Holmakefile"
        d = self.decide({path: ("5" * 40, "6" * 40)})
        self.assertEqual(d["tree"][path][0], "unloaded")

    def test_a_project_file_is_a_build_file_wherever_it_is(self):
        # Holmake reads holproject.toml beside the directories it visits,
        # which INCLUDES and project externals widen: the root file is a
        # build input of every cell, a file of that name in a directory
        # nothing loaded from is one too, and each needs an entry.
        other = "src/other/sub/holproject.toml"
        d = self.decide({other: ("5" * 40, "6" * 40)})
        self.assertEqual(d["tree"][other][0], "unattributed-build")
        self.assertEqual((d["status"], d["unaccounted"]),
                         ("different", [other]))
        path = "holproject.toml"
        d = self.decide({path: ("5" * 40, "6" * 40)})
        self.assertEqual(d["tree"][path][0], "unattributed-build")
        self.assertEqual((d["status"], d["unaccounted"]),
                         ("different", [path]))
        self.assertEqual(d["build_files"], {path: "unattributed-build"})
        reviewed = dict(path=path, kind="build", baseline_blob="5" * 40,
                        candidate_blob="6" * 40, reason="why",
                        gate="gate 5")
        d = self.decide({path: ("5" * 40, "6" * 40)},
                        entries=ENTRIES + [reviewed])
        self.assertEqual(d["tree"][path][0], "attributed")
        self.assertEqual(d["unaccounted"], [])
        # The committed table reviews the current difference.
        self.assertIn(path, [e["path"] for e in attr.load()["entries"]])

    def test_the_excluded_paths_are_not_read_from_either_commit(self):
        for path in ("src/simp/tests/performance/Foo.py",
                     "help/Docfiles/x.smd", "CLAUDE.md"):
            d = self.decide({path: ("5" * 40, "6" * 40)})
            self.assertEqual(d["tree"][path][0], "excluded", path)
            self.assertEqual(d["unaccounted"], [], path)

    def test_a_build_tool_or_sequence_needs_an_entry(self):
        for path in ("tools/sequences/base-hol", "tools/Holmake/Foo.sml",
                     "tools-poly/build.sml", "bin/build"):
            d = self.decide({path: ("5" * 40, "6" * 40)})
            self.assertEqual(d["tree"][path][0], "unattributed-build", path)
            self.assertEqual((d["status"], d["unaccounted"]),
                             ("different", [path]), path)
            self.assertEqual(g.status_code(d), 1)
        path = "tools/sequences/base-hol"
        build = dict(path=path, kind="build", baseline_blob="5" * 40,
                     candidate_blob="6" * 40, reason="a sequence",
                     gate="gate 5")
        d = self.decide({path: ("5" * 40, "6" * 40)},
                        entries=ENTRIES + [build])
        self.assertEqual(d["tree"][path][0], "attributed")
        self.assertEqual((d["status"], d["unaccounted"]), ("attributed", []))

    def test_a_path_the_receipts_do_not_show_loaded_is_not_different(self):
        for path in ("Manual/Developers/x.md",
                     "src/simp/tests/compatibility/inputs/x.sml"):
            d = self.decide({path: ("5" * 40, "6" * 40)})
            self.assertEqual(d["tree"][path][0], "unloaded", path)
            self.assertEqual(d["unaccounted"], [], path)

    def test_the_tree_is_the_whole_repository(self):
        with mock.patch.object(g.tg, "git_difference", mock.Mock(
                return_value=[["M", "tools/sequences/base-hol"]])) as diff:
            tree = g.source_tree("repo", "b", "c")
        diff.assert_called_once_with("repo", "b", "c", ".")
        self.assertEqual(tree, dict(tree=".", changes=[
            ["M", "tools/sequences/base-hol"]]))

    def test_an_entry_with_other_blobs_than_git_is_a_mismatch(self):
        d = self.decide({"src/simp/src/Cond_rewr.sig": ("5" * 40, "6" * 40)})
        self.assertEqual(d["tree"]["src/simp/src/Cond_rewr.sig"][0],
                         "mismatch")
        self.assertEqual(d["status"], "different")


class Code(unittest.TestCase):
    def test_the_identity_code_is_sealed_with_the_modules_it_uses(self):
        for name in ("timing_grid.py", "matrix_schema.py",
                     "task31_attribution.py", "task31_snapshot.py"):
            self.assertIn(name, g.IDENTITY_CODE)
            self.assertTrue((a.HERE / name).is_file())

    def test_the_recorded_seals_are_checked(self):
        g.check_code(g.code_seals())
        bad = dict(g.code_seals(), **{"task31_grid.py": {"sha256": "0"}})
        with self.assertRaises(ValueError):
            g.check_code(bad)
        with mock.patch.dict(g.CODE_HISTORY, {
                "task31_grid.py": [{"sha256": "0"}]}):
            g.check_code(bad)
        with self.assertRaises(ValueError):
            g.check_code({})


class Tables(unittest.TestCase):
    def test_a_placeholder_blob_is_refused_by_identity(self):
        document = copy.deepcopy(
            g.attribution(argparse.Namespace(attributed=None), False))
        document["entries"][0]["candidate_blob"] = None
        args = argparse.Namespace(repo=a.HERE.parents[3], baseline=BASE,
                                  candidate=BASE)
        self.assertTrue(g.attr.unfilled(document["entries"]))
        with self.assertRaises(ValueError) as caught:
            g.prepare_table(args, document)
        self.assertIn("placeholder", str(caught.exception))


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

        def cell(folder, case, size, baseline, candidate, samples=3,
                 entries=()):
            text = (Path(folder) / "cell").read_text()
            self.assertEqual(text, "%s %d\n" % (case, size))
            return row(case, size, self.status.get(
                g.name_of(case, size), "identical"), entries=entries)

        self.patches = [
            mock.patch.object(g, "run_one", run_one),
            mock.patch.object(g.idt, "cell", cell),
            mock.patch.object(g, "source_tree", lambda r, b, cn: dict(
                tree="src", changes=[])),
            mock.patch.object(g, "source_blobs", self.blobs),
            mock.patch.object(g, "prepare_table", lambda args, doc: None),
            mock.patch.object(g.ENGINE.h, "locked", self.locked),
            mock.patch.object(g.ENGINE.h, "attempts_file",
                              lambda args, appending, create=True:
                              self.root / "attempts.jsonl")]
        for patch in self.patches:
            patch.start()
            self.addCleanup(patch.stop)

    @staticmethod
    def blobs(repo, baseline, candidate, entries, tree):
        found = {p: dict(baseline="b", candidate="b") for p in c.SOURCES}
        found.update({e["path"]: dict(baseline=e["baseline_blob"],
                                      candidate=e["candidate_blob"])
                      for e in entries})
        return found

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
                         "attributed")
        flags = self.commands[0]
        self.assertTrue(flags[1].endswith("task31_snapshot.py"))
        self.assertEqual(flags[flags.index("--performance-pairs") + 1], "1")
        self.assertEqual(flags[flags.index("--batch-seconds") + 1], "1.0")
        self.assertGreaterEqual(g.ID_SECONDS, 1.0)
        self.assertEqual(
            timing.TABLE.seconds_map()["traversal_construct-0"],
            timing.LONG_SECONDS)
        self.assertNotIn("--batch-iterations", flags)
        code, text = self.main(["identity-replay", "--output", str(out),
                                "--repo", str(self.repo)])
        self.assertEqual(code, 0, text)

    def test_the_whole_grid_is_bound_to_the_checkout_and_replayed(self):
        checkout = dict(head=CAND, tree_outside_performance="t" * 40)
        calls = []
        with mock.patch.object(g.ENGINE.h, "bind_checkout", lambda *a_: (
                calls.append("bind") or dict(checkout))), \
                mock.patch.object(g.ENGINE.h, "recheck", lambda *a_: (
                    calls.append("recheck"))), \
                mock.patch.object(g.ENGINE.h, "judge_end", lambda *a_: (
                    calls.append("judge"))), \
                mock.patch.object(g.ENGINE.h, "check_checkout", lambda *a_:
                                  calls.append("check")):
            argv, out = self.args()
            code, text = self.main(argv)
            self.assertEqual(code, 0, text)
            decisions = a.load(out / "decisions.json")
            self.assertEqual(sum(decisions["counts"].values()), 278)
            self.assertEqual(decisions["counts"]["unresolved"], 0)
            self.assertEqual(a.load(out / "inventory.json")["checkout"],
                             checkout)
            self.assertEqual(calls, ["bind", "recheck", "judge"])
            code, text = self.main(["identity-replay", "--output",
                                    str(out), "--repo", str(self.repo)])
            self.assertEqual(code, 0, text)
            self.assertEqual(calls[-1], "check")

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

    @contextlib.contextmanager
    def whole_grid(self):
        """Everything a full grid needs but the code under test: the
        checkout is bound, rechecked and judged by stand-ins."""
        checkout = dict(head=CAND, tree_outside_performance="t" * 40)
        with mock.patch.object(g.ENGINE.h, "bind_checkout", lambda *a_:
                               dict(checkout)), \
                mock.patch.object(g.ENGINE.h, "recheck", lambda *a_: None), \
                mock.patch.object(g.ENGINE.h, "judge_end", lambda *a_:
                                  None), \
                mock.patch.object(g.ENGINE.h, "check_checkout", lambda *a_:
                                  None):
            yield

    def refused(self, argv, why):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            code, text = self.main(argv)
        self.assertEqual(code, tg.REFUSED, text)
        self.assertIn(why, err.getvalue())

    def test_another_table_is_for_diagnostics_only(self):
        other = self.repo / "other.json"
        other.write_text(attr.FILE.read_text() + "\n")
        why = "--attributed is for diagnostics"
        # The rule itself, on a full grid and on a diagnostic.
        with self.assertRaisesRegex(ValueError, why):
            g.attribution(argparse.Namespace(attributed=other), False)
        self.assertEqual(g.attribution(
            argparse.Namespace(attributed=other), True)["seal"],
            a.seal(other))
        self.assertEqual(g.attribution(
            argparse.Namespace(attributed=None), False)["seal"],
            a.seal(attr.FILE))
        # A full grid refuses it for that reason alone: with the table
        # left out it completes, with every other check satisfied.
        with self.whole_grid():
            argv, out = self.args()
            self.refused(argv + ["--attributed", str(other)], why)
            self.assertFalse(out.exists())
            code, text = self.main(argv)
            self.assertEqual(code, 0, text)
            replay = ["identity-replay", "--output", str(out), "--repo",
                      str(self.repo)]
            code, text = self.main(replay)
            self.assertEqual(code, 0, text)
            self.refused(replay + ["--attributed", str(other)], why)
        argv, out = self.args("traversal_construct-0", out="o2")
        code, text = self.main(argv + ["--attributed", str(other)])
        self.assertEqual(code, 0, text)
        recorded = a.load(out / "inventory.json")["attributed"]["file"]
        self.assertEqual(recorded, a.seal(other))

    def test_the_identity_module_offers_only_the_identity_commands(self):
        self.assertEqual(sorted(g.HANDLERS), [
            "identity", "identity-replay", "prepare", "sources"])
        help_ = io.StringIO()
        with contextlib.redirect_stdout(help_), \
                self.assertRaises(SystemExit):
            g.main(["--help"])
        self.assertIn("TASK31 gate 1", help_.getvalue())
        self.assertNotIn("timing of a stratified", help_.getvalue())
        for command in ("pilot", "predeclare", "verify-counts", "run",
                        "extend", "replay"):
            err = io.StringIO()
            with contextlib.redirect_stderr(err), \
                    self.assertRaises(SystemExit) as caught:
                g.main([command])
            self.assertEqual(caught.exception.code, 2, command)
            self.assertIn("invalid choice", err.getvalue())

    def test_the_committed_table_is_recorded_with_its_seal(self):
        argv, out = self.args("traversal_construct-0")
        self.assertEqual(self.main(argv)[0], 0)
        recorded = a.load(out / "inventory.json")["attributed"]["file"]
        self.assertEqual(recorded, a.seal(attr.FILE))

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

    def refuse_with(self, manifest, name="traversal_construct-0"):
        def fail(command, log, fds, timeout):
            folder = Path(command[command.index("--output") + 1])
            folder.mkdir()
            if manifest is not None:
                (folder / "manifest.json").write_text(manifest)
            Path(log).write_text("x")
            return dict(exit=1, timed_out=False)
        argv, out = self.args(name)
        err = io.StringIO()
        with mock.patch.object(g, "run_one", fail), \
                contextlib.redirect_stderr(err):
            code, text = self.main(argv)
        text += err.getvalue()
        self.assertEqual(code, tg.REFUSED, text)
        self.assertEqual(a.load(out / "inventory.json")["runs"], [])
        self.assertFalse((out / (name + ".json.xz")).exists())
        self.assertTrue((out / (name + ".json.xz.failed-1")).is_file())
        return argv, out, text

    def test_a_refusal_names_the_failure_of_the_runner(self):
        argv, out, text = self.refuse_with(json.dumps(
            dict(success=False, failure="batch too short; recalibrate")))
        self.assertIn("identity runner failed: traversal_construct-0: "
                      "batch too short; recalibrate", text)
        code, text = self.main(argv + ["--resume"])
        self.assertEqual(code, 0, text)
        self.assertTrue((out / "traversal_construct-0.json.xz").is_file())
        self.assertTrue((out / "traversal_construct-0.json.xz.failed-1")
                        .is_file())

    def test_a_manifest_without_a_failure_gives_the_plain_refusal(self):
        for manifest in (None, "not json", "[1]", "null", "{}",
                         json.dumps(dict(success=False))):
            with self.subTest(manifest=manifest):
                with tempfile.TemporaryDirectory() as tmp:
                    root = self.root
                    self.root = Path(tmp)
                    try:
                        _, _, text = self.refuse_with(manifest)
                    finally:
                        self.root = root
                self.assertIn("identity runner failed: "
                              "traversal_construct-0", text)
                self.assertNotIn("traversal_construct-0:", text)

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

    def test_the_attempts_ledger_holds_the_opening_and_the_close(self):
        argv, out = self.args("traversal_construct-0")
        self.assertEqual(self.main(argv)[0], 0)
        ledger = self.root / "attempts.jsonl"
        found = tg.Ledger(ledger).attempts(g.IDENTITY_TABLE)
        self.assertEqual(len(found), 1)
        self.assertEqual(g.attempt_counts(ledger, CAND), (1, 1))
        self.assertEqual(g.attempt_counts(ledger, BASE), (1, 0))
        code, text = self.main(["identity-replay", "--output", str(out),
                                "--repo", str(self.repo),
                                "--ledger", str(ledger)])
        self.assertEqual(code, 0, text)
        other = self.root / "other.jsonl"
        tg.ledger_append(other, event="open", stage="identity",
                         table=g.IDENTITY_TABLE, attempt="x",
                         candidate=CAND, output="o", checkout="c")
        code, _ = self.main(["identity-replay", "--output", str(out),
                             "--repo", str(self.repo),
                             "--ledger", str(other)])
        self.assertEqual(code, tg.REFUSED)

    def test_replay_judges_by_the_table_the_grid_recorded(self):
        argv, out = self.args("traversal_construct-0")
        self.main(argv)
        scratch = self.root / "other-table.json"
        document = json.loads(g.attr.FILE.read_text())
        document["entries"] = document["entries"][:-1]
        scratch.write_text(json.dumps(document))
        code, _ = self.main(["identity-replay", "--output", str(out),
                             "--repo", str(self.repo),
                             "--attributed", str(scratch)])
        self.assertEqual(code, tg.REFUSED)

    def test_the_sources_command_prints_what_the_cells_elaborated(self):
        argv, out = self.args("traversal_construct-0")
        self.main(argv)
        code, text = self.main(["sources", "--output", str(out)])
        self.assertEqual(code, 0)
        self.assertEqual(text.split(), sorted(c.SOURCES))
        code, text = self.main(["sources", "--output", str(out), "--heap"])
        self.assertEqual(text.split(), sorted(c.SOURCES))


if __name__ == "__main__":
    unittest.main()
