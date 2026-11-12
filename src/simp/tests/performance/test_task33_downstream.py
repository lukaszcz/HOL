#!/usr/bin/env python3
"""The TASK33 table of the timing driver (task32_downstream.py --table
task33) on fake trees and fake processes: table selection and the TASK32
table kept as it was, the `probe` unit kind (command, directory, digest,
watch and its refusals), the probe build, the cross-side loaded-set rule
(L1), the R floor and cap, and the interface the storage driver calls."""
import argparse
import contextlib
import io
import json
import math
import os
from pathlib import Path
import random
import shutil
import sys
import types
import unittest
from unittest import mock

import acceptance as a
import loading
import task33_cases as cases33
import task32_downstream as dw
import test_task32_downstream as t32
import test_task33_records as rt
from test_task32_downstream import World, Base, rows

setUpModule = t32.setUpModule


def heap_modules(heap):
    return ["Lib", "Thm"] if heap == "bin/hol.state0" else \
        ["Lib", "Thm", "boss"]


LOADS = dict(empty=[], first_use=[])
CHECK = {"load-simpLib": ["simpLib", "Traverse"],
         "load-congLib": ["congLib", "simpLib"]}


class World33(World):
    """Two fake snapshots for the TASK33 table: heaps, a sigobj and a few
    directories with make-deps, and a fake `launch` playing the probes."""

    DIRS = ("src/foo", "src/boss")

    def build_tree(self, root):
        (root / "bin").mkdir(parents=True)
        for n in ("Holmake", "hol", "hol.state0", "hol.state"):
            (root / "bin" / n).write_text("x")
        (root / "sigobj").mkdir()
        (root / "sigobj/Lib.ui").symlink_to(root / "bin/hol")
        for d in self.DIRS:
            (root / d / ".hol/make-deps").mkdir(parents=True)
            (root / d / ".hol/make-deps/a.d").write_text("deps\n")
        (root / "src/bare").mkdir()

    def write_manifest(self, **change):
        """The manifest lists the heaps among its products, with their
        sizes (the storage driver reports the saved-state bytes from
        them)."""
        super().write_manifest(**change)
        data = json.loads(self.manifest.read_text())
        for side in data["sides"].values():
            root = Path(side["root"])
            side["products"] = {
                str(p.relative_to(root)): dict(
                    bytes=p.stat().st_size, kind="file")
                for p in (root / "bin").glob("hol.state*")}
        self.manifest.write_text(json.dumps(data))

    def launch(self, argv, cwd, env, timeout, out_path, fds=()):
        side = "cand" if str(self.roots["cand"]) in argv[0] else "base"
        root = self.roots[side]
        cwd = Path(cwd)
        unit = cases33.BY_NAME[env["T33_KIND"]]
        assert "--holstate=" + str(root / unit["heap"]) in argv
        self.counter += 1
        self.calls.append((unit["name"], side, dict(env), list(argv),
                           str(cwd)))
        scale, noise = self.profile.get(unit["name"], self.default)
        rng = random.Random(self.counter)
        cpu = unit["serial"] * (scale if side == "cand" else 1.0) * (
            1 + noise * rng.uniform(-1, 1))
        if "T32_BUSY" in env and not self.ignore_busy:
            cpu += float(env["T32_BUSY"])
        fault = self.fault and self.fault(unit, side, self.counter)
        uo = argv[-2]
        loaded = list(CHECK.get(unit["name"], []))
        files = [["T32Report.sml", str(Path(uo).parent)],
                 ["T33Load.sml", str(cwd)]]
        files += [[m + ".sml", str(root / "src/foo")] for m in loaded]
        stats = dict(schema=dw.STATS_SCHEMA, nongc_usr=cpu * 0.9,
                     nongc_sys=cpu * 0.05, gc_usr=cpu * 0.04,
                     gc_sys=cpu * 0.01, gc_time=cpu * 0.05, holdir=str(root),
                     loaded_before=heap_modules(unit["heap"]),
                     loaded=loaded, files=files, **t32.STAT_FIELDS)
        out = self.output(unit, root, cwd, side == "cand" and
                          fault == "differ")
        if fault == "nocheck":
            out = "banner\n"
        if fault == "badjson":
            out += "@@T33\t{oops\n"
        if fault == "stray":
            (cwd / "stray.txt").write_text("x")
        if fault == "rootstray":
            (root / "src/foo/.hol/make-deps/new.txt").write_text("x")
        if fault == "rootmodify":
            (root / "src/foo/.hol/make-deps/a.d").write_text("changed\n")
        if fault == "churn":
            (root / "src/foo/.hol/make-deps/B.sml.d").write_text("d\n")
        if fault == "newhol":
            (root / "src/bare/.hol/make-deps").mkdir(parents=True)
        if fault == "sigobj":
            (root / "sigobj/New.ui").write_text("x")
        if fault == "extension" and side == "cand":
            stats["loaded"].append("simpExt")
        if fault == "less" and side == "cand" and stats["loaded"]:
            stats["loaded"].pop()
        if fault == "objs":
            stats["files"][1][1] = str(cwd / ".hol/objs")
        if fault == "misplaced_dir":
            stats["files"][2][1] = str(root) + "2/src"
        if fault == "misplaced_text":
            out = out.replace(str(root) + "/src", str(root) + "2/src")
            Path(out_path).write_text(out)
        if fault == "moved" and side == "cand" and stats["files"][2:]:
            stats["files"][2][1] = str(root / "src/elsewhere")
        if fault == "extra" and side == "cand":
            stats["loaded"].append("Zed")
        if fault == "flaky" and self.counter % 2:
            stats["loaded"].append("Flaky")
        Path(out_path).write_text(out)
        if fault != "nostats":
            Path(env["T32_STATS"]).write_text(json.dumps(stats) + "\n")
        return dict(exit=1 if fault == "exit" else 0, timed_out=False,
                    wall=cpu * 1.03, utime=cpu * 0.9, stime=cpu * 0.1,
                    maxrss=10 ** 8, survivors=[])

    @staticmethod
    def output(unit, root, probe_dir, differ=False):
        """What a probe of the unit prints: the well-formed records of its
        kind, with the root and the probe directory in the evidence (the
        digest masks them) and, when `differ`, other evidence."""
        run = rt.load_run("load", unit["env"]["T33_KIND"])
        for record in run:
            if record["record"] == "probe":
                record["holdir"] = str(root)
            if record["record"] == "check":
                record["value"] = "ok at %s/src, %s/T33Load.sml%s" % (
                    root, probe_dir, " (more)" if differ else "")
        return "banner\n" + rt.text(run, noise=False)

    @staticmethod
    def probes(root, folder, env, timeout, fds, sealed=None, modules=None):
        folder = Path(folder)
        seals = dw.code_seals()
        return dict(dir=str(folder), modules=["T33Load"], sources={
            Path(rel).name: seals[rel]["sha256"]
            for rel in dw.ACTIVE.probe_sources},
            build_stdout_sha256="0" * 64)

    def patches(self):
        return super().patches() + [
            mock.patch.object(dw, "build_probes", self.probes)]

    def spec(self, names, pairs=10, stage="first", seed=None, reps=1,
             busy=None):
        return dict(mode=stage, stage=stage, names=names,
                    pairs={w: pairs for w in names},
                    reps={w: reps for w in names},
                    seed=seed or dw.SEEDS[stage], references=None,
                    busy=busy)


class Base33(Base):
    def setUp(self):
        previous = dw.use_table("task33")
        self.addCleanup(dw.use_table, previous)
        self.dir = t32.tempfile.TemporaryDirectory(prefix="t33-test-")
        self.addCleanup(self.dir.cleanup)
        self.world = World33(self.dir.name)
        for patch in self.world.patches():
            patch.start()
            self.addCleanup(patch.stop)
        self.addCleanup(self.remove_lock)

    def smoke(self, name="s", names=None):
        if (self.world.tmp / name).exists():
            name += "x"
        args, spec = self.world.info(name, "smoke", names=names)
        return dw.run_stage(args, spec)


class TableSelection(unittest.TestCase):
    def setUp(self):
        self.addCleanup(dw.use_table, dw.use_table("task32"))

    def test_the_default_table_is_task32_and_keeps_its_constants(self):
        self.assertEqual(dw.ACTIVE.name, "task32")
        self.assertIs(dw.cases, t32.cases)
        self.assertEqual((dw.TABLE, dw.R_CAP, dw.MIN_UNIT_CPU,
                          dw.SAMPLE_CPU), ("task32-downstream", 4, 1.0, 0.0))
        self.assertEqual(dw.SEEDS, dict(
            smoke="task32-1-smoke", control="task32-1-control",
            pilot="task32-1-pilot", first="task32-1",
            second="task32-1-ext", followup="task32-1-fu"))
        self.assertEqual(dw.JOURNALS, ".agent-files/scratch/task32")
        self.assertEqual(dw.COUNTS.name, "task32_counts.json")
        self.assertEqual(dw.FOLLOWUP_COUNTS.name,
                         "task32_followup_counts.json")
        self.assertEqual(dw.CODE[:2], ("task32_cases.py",
                                       "task32_downstream.py"))
        self.assertEqual(
            dw.ledger_path("/r").parts[-3:], ("evidence", "task32",
                                              "attempts.jsonl"))
        self.assertEqual(dw.table_key(), {})

    def test_task33_selects_its_cases_seeds_ledger_and_limits(self):
        with dw.using_table("task33"):
            self.assertIs(dw.cases, cases33)
            self.assertEqual((dw.TABLE, dw.R_CAP, dw.MIN_UNIT_CPU,
                              dw.SAMPLE_CPU), ("task33-loading", 8, 0.2,
                                               1.0))
            self.assertEqual(dw.SEEDS, dict(
                smoke="task33-1-smoke", control="task33-1-control",
                pilot="task33-1-pilot", first="task33-1",
                second="task33-1-ext", followup="task33-1-fu"))
            self.assertEqual(dw.JOURNALS, ".agent-files/scratch/task33")
            self.assertEqual(dw.COUNTS.name, "task33_counts.json")
            self.assertEqual(dw.CODE[:2], ("task33_cases.py",
                                           "task32_downstream.py"))
            self.assertEqual(
                dw.ledger_path("/r").parts[-3:], ("evidence", "task33",
                                                  "attempts.jsonl"))
            self.assertEqual(dw.table_key(), {"table": "task33"})
            self.assertEqual(cases33.CONTROL_UNIT, "load-simpLib")
        self.assertEqual(dw.ACTIVE.name, "task32")
        self.assertIs(dw.cases, t32.cases)

    def test_an_unknown_table_is_refused(self):
        with self.assertRaisesRegex(dw.Refusal, "unknown table"):
            dw.use_table("task99")

    def test_main_selects_the_table_before_it_builds_the_parser(self):
        dw.select_table(["--table", "task33", "replay", "x"])
        self.assertEqual(dw.ACTIVE.name, "task33")
        self.assertEqual(dw.build_parser().parse_args(
            ["--table", "task33", "smoke", "--repo", "r", "--base-root",
             "b", "--cand-root", "c", "--manifest", "m", "--output",
             "o"]).scratch, Path("/dev/shm/t33"))
        dw.select_table(["replay", "x"])
        self.assertEqual(dw.ACTIVE.name, "task32")
        self.assertEqual(dw.build_parser().parse_args(
            ["smoke", "--repo", "r", "--base-root", "b", "--cand-root",
             "c", "--manifest", "m", "--output", "o"]).scratch,
            Path("/dev/shm/t32"))
        out = io.StringIO()
        with contextlib.redirect_stderr(out), \
                self.assertRaises(SystemExit):
            dw.select_table(["--table", "nope", "replay", "x"])

    def test_the_task33_cases_are_five_probe_units(self):
        self.assertEqual(cases33.NAMES, (
            "state0-empty", "state-empty", "load-simpLib", "load-congLib",
            "first-use"))
        for unit in cases33.UNITS:
            self.assertEqual(unit["kind"], "probe")
            self.assertEqual(unit["probe"], "T33Load")
            self.assertIn("T33_KIND", unit["env"])
        self.assertEqual(cases33.HEAPS, ("bin/hol.state",
                                         "bin/hol.state0"))
        self.assertEqual(cases33.PROBES, ("T33Load",))
        self.assertEqual(cases33.BY_NAME["load-congLib"]["env"],
                         dict(T33_KIND="load-congLib",
                              T33_MODULE="congLib"))
        self.assertEqual(cases33.BY_NAME["state0-empty"]["env"],
                         dict(T33_KIND="state0-empty"))
        for unit in cases33.UNITS:  # the record kind is the unit's name
            self.assertEqual(unit["env"]["T33_KIND"], unit["name"])
            self.assertIn(unit["name"], cases33.records.LOAD_KINDS)
        self.assertNotIn("T33_MODULE", cases33.BY_NAME["first-use"]["env"])

    def test_the_history_of_task32_keeps_every_entry_and_task33_has_none(
            self):
        self.assertEqual(len(dw.TABLES["task32"].history[
            "task32_downstream.py"]), 3)
        self.assertEqual(dw.TABLES["task33"].history, {})

    def test_a_counts_file_of_another_table_is_refused(self):
        with tempfile_dir() as tmp:
            path = Path(tmp, "c.json")
            path.write_text(json.dumps(dict(
                schema=dw.COUNTS_SCHEMA, kind="first", table="task33")))
            with self.assertRaisesRegex(dw.Refusal, "of table task33"):
                dw.load_counts(path, {}, "first")


def tempfile_dir():
    return t32.tempfile.TemporaryDirectory()


class Probe(Base33):
    def test_the_command_directory_environment_and_digest(self):
        report = self.smoke()
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(report["table"], "task33")
        self.assertEqual(report["claims"], dw.ACTIVE.claims)
        self.assertEqual(len(report["runs"]), 10)
        self.assertEqual(set(report["probes"]), {"base", "cand"})
        for name, side, env, argv, cwd in self.world.calls:
            unit = cases33.BY_NAME[name]
            root = self.world.roots[side]
            reporter = Path(report["reporter"][side]["uo"])
            self.assertEqual(argv, [
                str(root / "bin/hol"), "--gcthreads=1", "run",
                "--holstate=" + str(root / unit["heap"]), str(reporter),
                "T33Load"])
            self.assertEqual(cwd, str(reporter.parent))
            self.assertEqual(env["T33_KIND"], unit["env"]["T33_KIND"])
            self.assertEqual(env.get("T33_MODULE"),
                             unit["env"].get("T33_MODULE"))
            self.assertNotIn("POLY_CLINE_OPTIONS", env)
            self.assertTrue(env["T32_STATS"].endswith(".stats"))
            self.assertFalse(cwd.startswith(str(root)))
        digests = report["outcome"]["digests"]
        self.assertEqual(set(digests), set(cases33.NAMES))
        # the empty kinds print no check: the digest of no lines
        self.assertEqual(digests["state0-empty"], dw.sha(b""))
        self.assertNotEqual(digests["load-simpLib"], dw.sha(b""))
        self.assertTrue(report["outcome"]["probe"]["ok"])
        self.assertTrue(report["outcome"]["probe"]["complete"])
        self.assertEqual(report["prebuilt"], {n: None
                                              for n in cases33.NAMES})
        info, again = dw.replay_one(self.world.tmp / "s",
                                    ledger=self.world.ledger())
        self.assertEqual(dw.dumps(again), dw.dumps(report))

    def test_a_task33_run_is_refused_by_a_replay_under_task32(self):
        self.smoke()
        with dw.using_table("task32"):
            with self.assertRaisesRegex(dw.Refusal, "of table task33"):
                dw.replay_one(self.world.tmp / "s",
                              ledger=self.world.ledger())

    def test_the_receipt_has_stdout_stats_and_the_digest(self):
        report = self.smoke(names=["load-simpLib"])
        receipt = a.load(self.world.tmp / "s" / report["runs"][0]["receipt"])
        self.assertIn("@@T33\t", receipt["stdout"])
        self.assertEqual(receipt["stats"]["gc_full"], 1)
        self.assertEqual(receipt["env"]["T33_MODULE"], "simpLib")
        self.assertEqual(receipt["digest"], report["outcome"]["digests"][
            "load-simpLib"])

    def test_each_table_names_its_digest_and_gets_the_roots(self):
        table = dw.ACTIVE
        hook = mock.Mock(return_value="d" * 64)
        with mock.patch.object(dw, "ACTIVE", dataclass_replace(
                table, probe_digest=hook)):
            report = self.smoke(names=["state-empty"])
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(report["outcome"]["digests"],
                         {"state-empty": "d" * 64})
        self.assertEqual(hook.call_count, 2)
        for call, side in zip(hook.call_args_list, ("base", "cand")):
            text, root, probe_dir, unit = call.args
            self.assertIn("@@T33", text)
            self.assertEqual(root, self.world.roots[side])
            self.assertEqual(Path(probe_dir).name, "probe-" + side)
            self.assertEqual(unit["name"], "state-empty")

    def test_launch_probe_is_the_interface_of_a_stage(self):
        scratch = self.world.tmp / "ctx"
        for sub in ("home", "tmp", "out"):
            (scratch / sub).mkdir(parents=True)
        made = dw.make_ctx(
            {s: dict(root=r) for s, r in self.world.roots.items()},
            scratch, 60, (), self.world.tmp / "j", "attempt-1",
            self.world.tmp / "ev")
        for side in ("base", "cand"):
            made["reporter"][side] = self.world.reporter(
                None, scratch / ("probe-" + side), {}, 60, ())
        unit = dict(cases33.BY_NAME["load-congLib"], name="registry-x")
        self.world.default = (1.0, 0.0)
        got = dw.launch_probe(made, "base", unit, "reg-base-00")
        self.assertTrue(got["accepted"], got.get("rejection"))
        self.assertEqual(got["workload"], "registry-x")
        self.assertIn("@@T33", got["stdout"])
        self.assertEqual(len(got["digest"]), 64)
        self.assertEqual(got["stats"]["holdir"],
                         str(self.world.roots["base"]))

    def test_open_attempt_and_table_lines_take_a_ledger_table(self):
        path = self.world.tmp / "led" / "attempts.jsonl"
        one = dw.open_attempt(path, "info", mode="smoke", key="k", seed="s",
                              output="o", checkout="c")
        two = dw.open_attempt(path, "info", table="task33-storage",
                              mode="smoke", key="k", seed="s", output="o",
                              checkout="c")
        state = dw.tg.Ledger(path)
        self.assertEqual([r["attempt"] for r in dw.table_lines(state)],
                         [one])
        self.assertEqual([r["attempt"] for r in dw.table_lines(
            state, "task33-storage")], [two])
        self.assertEqual({r["table"] for r in state.records},
                         {"task33-loading", "task33-storage"})


def dataclass_replace(table, **changes):
    import dataclasses
    return dataclasses.replace(table, **changes)


class ProbeRefusals(Base33):
    def refused(self, fault, regex, names=("load-simpLib",), blocked=False,
                only_side=None):
        self.world.fault = lambda unit, side, n: (
            fault if only_side in (None, side) else None)
        report = self.smoke(names=list(names))
        self.assertFalse(report["success"])
        self.assertRegex(report["failure"], regex)
        self.assertEqual(bool(report.get("blocked")), blocked,
                         report["failure"])
        return report

    def test_a_stray_write_in_the_probe_directory(self):
        self.refused("stray", "stray write.*stray.txt")

    def test_a_stray_write_in_the_snapshot(self):
        self.refused("rootstray", "stray write")
        self.refused("sigobj", "stray write")
        self.assertFalse((self.world.roots["base"] /
                          "src/foo/.hol/make-deps/new.txt").exists())

    def test_a_modified_make_deps_file_in_the_snapshot(self):
        self.refused("rootmodify", "modified existing file")

    def test_make_deps_churn_in_the_snapshot(self):
        report = self.refused("churn", "wrote Holmake cache")
        self.assertFalse((self.world.roots["base"] /
                          "src/foo/.hol/make-deps/B.sml.d").exists())
        self.assertTrue(report["runs"])

    def test_a_dot_hol_in_a_bare_directory(self):
        self.refused("newhol", "stray write")
        self.assertFalse((self.world.roots["base"] /
                          "src/bare/.hol").exists())

    def test_missing_stats(self):
        self.refused("nostats", "missing stats")

    def test_a_failing_process(self):
        self.refused("exit", "process failed")

    def test_no_check_record_where_one_is_owed(self):
        self.refused("nocheck", "first record is not the probe header")

    def test_an_unreadable_record(self):
        self.refused("badjson", "bad JSON in a @@T33 line")

    def test_an_extension_module_is_a_finding_about_the_candidate(self):
        self.refused("extension", "extension module", blocked=True,
                     only_side="cand")

    def test_an_extension_module_on_the_baseline_is_a_refusal(self):
        self.world.fault = lambda unit, side, n: (
            "extension" if side == "base" else None)
        # the fake adds it on the candidate only: add it to base directly
        original = self.world.launch

        def launch(argv, cwd, env, timeout, out_path, fds=()):
            done = original(argv, cwd, env, timeout, out_path, fds)
            stats = json.loads(Path(env["T32_STATS"]).read_text())
            stats["loaded"].append("splitExt")
            Path(env["T32_STATS"]).write_text(json.dumps(stats) + "\n")
            return done
        with mock.patch.object(dw, "launch", launch):
            report = self.smoke(names=["load-simpLib"])
        self.assertFalse(report["success"])
        self.assertRegex(report["failure"], "extension module")
        self.assertFalse(report.get("blocked"))

    def test_outputs_that_differ_between_the_sides(self):
        self.world.fault = lambda unit, side, n: "differ"
        report = self.smoke(names=["load-simpLib"])
        self.assertFalse(report["success"])
        self.assertRegex(report["failure"], "outputs differ")

    def test_a_candidate_that_loads_fewer_modules_is_blocked(self):
        # check_new_stems alone would pass this (nothing extra)
        report = self.refused("less", "differ from the baseline's",
                              blocked=True)
        self.assertRegex(report["failure"], "loaded")

    def test_a_candidate_that_loads_a_file_from_another_directory(self):
        self.refused("moved", "differ from the baseline's", blocked=True)

    def test_a_candidate_with_an_extra_module_is_blocked_either_way(self):
        self.refused("extra", "loaded what no baseline", blocked=True)

    def test_processes_of_a_side_that_load_differently_are_refused(self):
        self.world.fault = lambda unit, side, n: "flaky"
        args, spec = self.world.info("f", "pilot", names=["load-simpLib"])
        report = dw.run_stage(args, spec)
        self.assertFalse(report["success"])
        self.assertRegex(report["failure"], "loaded different modules")

    def test_the_masked_view_ignores_the_roots_and_probe_directories(self):
        report = self.smoke(names=["load-simpLib"])
        self.assertTrue(report["success"])
        receipts = [a.load(self.world.tmp / "s" / r["receipt"])
                    for r in report["runs"]]
        views = [dw.masked_view(r, report["roots"][r["side"]],
                                report["reporter"][r["side"]]["dir"])
                 for r in receipts]
        self.assertEqual(views[0], views[1])
        self.assertIn(["T33Load.sml", "<PROBE>"], views[0]["files"])
        self.assertIn(["simpLib.sml", "<ROOT>/src/foo"], views[0]["files"])

    def test_a_path_with_a_misplaced_prefix_is_refused(self):
        # in the loaded files (the probe directory's `.hol/objs` copy is
        # not a logical directory) and in the output text
        self.refused("objs", "outside the root")

    def test_a_directory_with_a_misplaced_root_is_refused(self):
        self.refused("misplaced_dir", "misplaced form")

    def test_an_output_with_a_misplaced_probe_path_is_refused(self):
        self.refused("misplaced_text", "misplaced form")

    def test_the_task32_table_does_not_apply_the_rule(self):
        # the rule is a field of the table: without it a candidate that
        # loads less is not blocked
        with mock.patch.object(dw, "ACTIVE", dataclass_replace(
                dw.ACTIVE, cross_side=False)):
            self.world.fault = lambda unit, side, n: "less"
            report = self.smoke(names=["load-simpLib"])
        self.assertTrue(report["success"], report.get("failure"))


class BuildProbes(unittest.TestCase):
    NAMES = ("sub/T33Load.sml", "sub/T33Load.ML", "T33Registry.sml",
             "T33Graph.sml")

    def setUp(self):
        self.addCleanup(dw.use_table, dw.use_table("task33"))
        self.tmp = t32.tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.src = Path(self.tmp.name, "src")
        (self.src / "sub").mkdir(parents=True)
        for rel in self.NAMES:
            (self.src / rel).write_text("val _ = %d\n" % len(rel))
        self.seals = {rel: a.seal(self.src / rel) for rel in self.NAMES}
        self.folder = Path(self.tmp.name, "probe-base")
        self.folder.mkdir()
        self.root = Path(self.tmp.name, "base")
        self.calls = []
        table = dataclass_replace(dw.ACTIVE, probe_sources=self.NAMES)
        patch = mock.patch.object(dw, "ACTIVE", table)
        patch.start()
        self.addCleanup(patch.stop)

    def execute(self, argv, cwd, env, timeout, fds, exit=0, built=True):
        self.calls.append((argv, Path(cwd)))
        if built:
            for word in argv:
                if word.endswith(".uo"):
                    (Path(cwd) / ".hol/objs").mkdir(parents=True,
                                                    exist_ok=True)
                    (Path(cwd) / ".hol/objs" / word).write_text("x")
        return dict(exit=exit, timed_out=False, stdout="out",
                    stdout_sha256="1" * 64)

    def build(self, modules=("T33Load",), sealed=None, **kw):
        with mock.patch.object(
                loading, "execute", lambda *a_, **k: self.execute(
                    *a_, **kw)):
            return dw.build_probes(
                self.root, self.folder, {}, 60, (), base=self.src,
                modules=modules, sealed=self.seals if sealed is None
                else sealed)

    def test_sources_are_checked_copied_sealed_and_built_in_place(self):
        got = self.build()
        self.assertEqual(got["dir"], str(self.folder))
        self.assertEqual(got["sources"], {
            Path(rel).name: self.seals[rel]["sha256"]
            for rel in self.NAMES})
        # bare module names, no physical .uo path
        self.assertEqual(got["modules"], ["T33Load"])
        self.assertNotIn("uo", got)
        self.assertEqual((self.folder / "T33Load.ML").read_bytes(),
                         (self.src / "sub/T33Load.ML").read_bytes())
        argv, cwd = self.calls[0]
        self.assertEqual(argv, [str(self.root / "bin/Holmake"),
                                "--no-project", "--no-cache",
                                "T33Load.uo"])
        self.assertEqual(cwd, self.folder)

    def test_a_source_that_is_not_the_sealed_one_is_refused_before_a_build(
            self):
        (self.src / "T33Registry.sml").write_text("val _ = 99\n")
        with self.assertRaisesRegex(dw.Refusal, "T33Registry.sml is not "
                                    "the one sealed"):
            self.build()
        self.assertEqual(self.calls, [])
        self.assertEqual(list(self.folder.iterdir()), [])
        (self.src / "T33Registry.sml").write_text("val _ = %d\n" % len(
            "T33Registry.sml"))
        seals = dict(self.seals)
        del seals["T33Graph.sml"]
        with self.assertRaisesRegex(dw.Refusal, "T33Graph.sml is not "
                                    "the one sealed"):
            self.build(sealed=seals)

    def test_the_default_seals_are_the_code_seals_of_the_table(self):
        with mock.patch.object(dw, "code_seals", lambda: self.seals):
            with mock.patch.object(
                    loading, "execute", lambda *a_, **k: self.execute(
                        *a_, **k)):
                got = dw.build_probes(self.root, self.folder, {}, 60, (),
                                      base=self.src, modules=["T33Load"])
        self.assertEqual(got["modules"], ["T33Load"])

    def test_a_failed_build_or_a_missing_product_is_refused(self):
        with self.assertRaisesRegex(dw.Refusal, "probe build failed"):
            self.build(exit=2)
        shutil.rmtree(self.folder / ".hol")
        with self.assertRaisesRegex(dw.Refusal, "was not built"):
            self.build(built=False)

    def test_missing_modules_and_sources_are_refused(self):
        with self.assertRaisesRegex(dw.Refusal, "no source T33Ext.sml"):
            self.build(modules=("T33Load", "T33Ext"))
        with self.assertRaisesRegex(dw.Refusal, "no probe modules"):
            self.build(modules=())
        (self.src / "sub/T33Load.sml").unlink()
        with self.assertRaises(OSError):
            self.build()

    def test_a_source_named_like_the_reporter_or_twice_is_refused(self):
        for names, message in ((self.NAMES + ("T32Report.sml",),
                                "named like the reporter"),
                               (self.NAMES + ("other/T33Load.sml",),
                                "two probe sources")):
            table = dataclass_replace(dw.ACTIVE, probe_sources=names)
            with mock.patch.object(dw, "ACTIVE", table):
                with self.assertRaisesRegex(dw.Refusal, message):
                    self.build()

    def test_the_modules_to_build_can_be_named(self):
        got = self.build(modules=("T33Registry", "T33Graph"))
        self.assertEqual(got["modules"], ["T33Registry", "T33Graph"])
        argv, cwd = self.calls[-1]
        self.assertEqual(argv[-2:], ["T33Registry.uo", "T33Graph.uo"])
        self.assertNotIn("T33Load.uo", argv)

    def test_a_table_without_probe_sources_refuses(self):
        with dw.using_table("task32"):
            with self.assertRaisesRegex(dw.Refusal, "no probe sources"):
                dw.build_probes(self.root, self.folder, {}, 60, ())


class RealProbeSources(unittest.TestCase):
    def test_the_probe_files_are_the_directory_and_runtimemetrics(self):
        found = sorted(p.name for p in (dw.HERE / "task33").iterdir())
        self.assertEqual(sorted(Path(f).name for f in
                                cases33.PROBE_FILES if f.startswith(
                                    "task33/")), found)
        self.assertIn("RuntimeMetrics.sml", cases33.PROBE_FILES)
        for rel in cases33.PROBE_FILES:
            self.assertTrue((dw.HERE / rel).is_file(), rel)

    def test_the_table_code_has_the_probe_sources_and_the_parser(self):
        code = dw.TABLES["task33"].code
        for rel in cases33.PROBE_FILES + ("task33_records.py",):
            self.assertIn(rel, code)
        self.assertEqual(len(set(code)), len(code))
        self.assertEqual(dw.TABLES["task33"].probe_sources,
                         cases33.PROBE_FILES)

    def test_task32_has_neither_probe_sources_nor_a_digest(self):
        table = dw.TABLES["task32"]
        self.assertIsNone(table.probe_sources)
        self.assertIsNone(table.probe_digest)
        self.assertFalse(any("task33" in n for n in table.code))
        self.assertIs(dw.TABLES["task33"].probe_digest, cases33.digest)
        self.assertFalse(hasattr(dw, "set_probe_digest"))
        self.assertFalse(hasattr(dw, "check_records_digest"))


class Sizing(unittest.TestCase):
    def setUp(self):
        self.addCleanup(dw.use_table, dw.use_table("task33"))

    def pilot(self, cpu, noise=0.0):
        return dw.pilot_summary({"u": rows(
            lambda i: cpu * (1 + noise * (-1) ** i), lambda i: cpu,
            pairs=10)})["u"]

    def test_r_is_at_least_one_second_of_cpu(self):
        for cpu, want in ((0.25, 4), (0.3, 4), (0.6, 2), (1.5, 1),
                          (0.2, 5)):
            got = self.pilot(cpu)
            self.assertEqual(got["reps"], want, cpu)
            self.assertTrue(got["long_enough"])
            self.assertTrue(got["within_cap"])

    def unsized(self, name, cpu):
        """A pilot unit whose jitter sized no R (no gated metric had a
        usable log ratio, so `required_units` is None)."""
        real = loading.jitter

        def jitter(*args):
            return dict(real(*args), required_units=None)
        with mock.patch.object(loading, "jitter", jitter):
            return dw.pilot_summary({name: rows(
                lambda i: cpu, lambda i: cpu, pairs=10)})[name]

    def test_the_floor_applies_to_the_declared_sample(self):
        # a 0.07 s kind at R 15 is declared at 8: 8 * 0.07 = 0.56 s
        got = self.pilot(0.07)
        self.assertEqual(got["reps"], 15)
        self.assertTrue(got["long_enough"])
        self.assertAlmostEqual(got["floor_cpu"], 0.56)
        outcome = dict(covered=True, pilot=dict(u=got))
        self.assertEqual(dw.declared_reps(outcome), dict(u=8))

    def test_a_sample_under_the_floor_even_at_the_cap_is_not_long_enough(
            self):
        got = self.pilot(0.02)
        self.assertEqual(got["reps"], 50)
        self.assertFalse(got["long_enough"])
        self.assertAlmostEqual(got["floor_cpu"], 0.16)
        self.assertTrue(self.pilot(0.025)["long_enough"])
        with self.assertRaisesRegex(
                dw.Refusal, r"under 0\.2 s of CPU per declared sample: u "
                r"\(median_cpu 0\.02 s, floor_cpu 0\.16 s, reps 50\)"):
            dw.declared_reps(dict(covered=False, pilot=dict(u=got)))

    def test_a_unit_whose_jitter_sized_no_r_is_not_covered(self):
        for table, keys in (("task33", True), ("task32", False)):
            with dw.using_table(table):
                got = self.unsized("u", 0.5)
                self.assertIsNone(got["reps"])
                self.assertFalse(got["long_enough"])
                self.assertFalse(got["within_cap"])
                self.assertEqual("floor_cpu" in got, keys)
                if keys:
                    self.assertIsNone(got["floor_cpu"])
                outcome = dict(covered=False, pilot=dict(u=got))
                under, unsized = dw.uncovered_units(outcome)
                self.assertTrue(unsized)
                # a process floor is judged without R: 0.5 s < 1 s too
                self.assertEqual(bool(under), not keys)
                with self.assertRaisesRegex(
                        dw.Refusal, r"jitter sized no R: u \(median_cpu "
                        r"0\.5 s.*reps None\)"):
                    dw.declared_reps(outcome)

    def test_both_causes_are_named_with_their_units(self):
        short = self.pilot(0.02)
        none = self.unsized("v", 0.5)
        outcome = dict(covered=False, pilot=dict(u=short, v=none))
        text = dw.pilot_refusal("--pilot", outcome)
        self.assertTrue(text.startswith("--pilot is not usable: under "
                                        "0.2 s of CPU per declared sample"))
        self.assertIn("u (median_cpu 0.02 s, floor_cpu 0.16 s, reps 50)",
                      text)
        self.assertIn("; jitter sized no R: v (median_cpu 0.5 s, reps None)",
                      text)

    def test_the_summary_line_names_an_uncovered_pilot(self):
        with dw.using_table("task32"):
            report = dict(mode="pilot", stage=None, attempt=1, runs=[],
                          success=True, outcome=dict(
                              covered=False, pilot=dict(u=self.pilot(0.5))))
            text = dw.summary_line(report)
        self.assertIn("not covered: under 1 s of CPU per process: u "
                      "(median_cpu 0.5 s, reps 1)", text)
        report["outcome"] = dict(covered=True, pilot={})
        self.assertNotIn("not covered", dw.summary_line(report))

    def test_the_pilot_dict_of_a_process_floor_table_keeps_its_keys(self):
        with dw.using_table("task32"):
            self.assertEqual(set(self.pilot(1.5)), {
                "jitter", "median_cpu", "median_wall", "reps",
                "long_enough", "within_cap"})

    def test_the_refusals_name_the_kind_of_the_floor(self):
        self.assertEqual(dw.floor_text(), "0.2 s of CPU per declared sample")
        with dw.using_table("task32"):
            self.assertEqual(dw.floor_text(), "1 s of CPU per process")
            with self.assertRaisesRegex(Exception, "1 s of CPU per process"):
                dw.declared_reps(dict(covered=False, pilot={}))

    def test_a_process_floor_table_is_unchanged_and_has_no_floor_cpu(self):
        with dw.using_table("task32"):
            got = self.pilot(0.5)
            self.assertFalse(got["long_enough"])
            self.assertNotIn("floor_cpu", got)
            self.assertTrue(self.pilot(1.0)["long_enough"])

    def test_the_unit_floor_of_each_table_and_its_validation(self):
        self.assertEqual(dw.UNIT_FLOOR, "sample")
        with dw.using_table("task32"):
            self.assertEqual(dw.UNIT_FLOOR, "process")
        for bad in ("unit", "", None):
            with self.assertRaises(ValueError):
                dataclass_replace(dw.TABLES["task33"], unit_floor=bad)

    def test_noise_raises_r_above_the_floor_and_the_cap_clamps_it(self):
        got = self.pilot(0.25, noise=0.5)
        self.assertGreater(got["reps"], 4)
        outcome = dict(covered=True, pilot=dict(
            a=dict(reps=20), b=dict(reps=3)))
        self.assertEqual(dw.declared_reps(outcome), dict(a=8, b=3))

    def test_the_same_pilot_is_sized_by_each_tables_own_floor(self):
        # 0.25 s of CPU: the task33 table asks for ceil(1 / 0.25) = 4
        # processes per sample; the task32 table has no floor, R comes
        # from the jitter alone (and its unit floor is one second)
        for noise in (0.0, 0.5):
            need = {}
            for table in ("task32", "task33"):
                with dw.using_table(table):
                    got = self.pilot(0.25, noise=noise)
                    need[table] = max(1, math.ceil(
                        got["jitter"]["required_units"] / dw.PAIRS))
                    self.assertEqual(got["reps"], need[table] if table ==
                                     "task32" else max(4, need[table]),
                                     (table, noise))
                    self.assertEqual(got["long_enough"],
                                     table == "task33")
            self.assertEqual(need["task32"], need["task33"])
        with dw.using_table("task32"):
            self.assertEqual(self.pilot(0.25)["reps"], 1)
        self.assertEqual(self.pilot(0.25)["reps"], 4)

    def test_the_cap_of_each_table(self):
        outcome = dict(covered=True, pilot=dict(a=dict(reps=20)))
        with dw.using_table("task32"):
            self.assertEqual(dw.declared_reps(outcome), dict(a=4))
        self.assertEqual(dw.declared_reps(outcome), dict(a=8))

    def test_a_pilot_run_on_the_fake_sizes_r_from_the_floor(self):
        self.addCleanup(self.cleanup)
        self.tmp = t32.tempfile.TemporaryDirectory()
        world = World33(self.tmp.name)
        self.patches = world.patches()
        for patch in self.patches:
            patch.start()
        world.default = (1.0, 0.0)
        args, spec = world.info("p", "pilot")
        report = dw.run_stage(args, spec)
        self.assertTrue(report["success"], report.get("failure"))
        self.assertTrue(report["outcome"]["covered"])
        for name, found in report["outcome"]["pilot"].items():
            want = -(-1.0 // found["median_cpu"])
            self.assertGreaterEqual(found["reps"], want, name)
        self.assertEqual(
            dw.declared_reps(report["outcome"])["state0-empty"], 4)

    def cleanup(self):
        for patch in getattr(self, "patches", []):
            patch.stop()
        self.tmp.cleanup()
        for lock in Path(self.tmp.name, "repo", ".agent-files").glob(
                "*.lock"):
            lock.unlink()


STORAGE = "task33-storage"


class LedgerTables(Base33):
    """The ledger table travels with the attempt: two tools (the loading
    driver and S4's storage driver) keep their attempts in one file."""

    def setUp(self):
        super().setUp()
        self.path = self.world.tmp / "led" / "attempts.jsonl"
        self.output = self.world.tmp / "out"
        self.output.mkdir()

    def opened(self, table=None, stage="first", key="k"):
        return dw.open_attempt(
            self.path, "open", table=table, stage=stage, key=key,
            seed="s", output=str(self.output), checkout="c",
            first_attempt=None, counts=None)

    def report(self, attempt, stage="first", mode="first"):
        return dict(attempt=attempt, stage=stage, mode=mode, success=False)

    def tables(self):
        return [(r["event"], r["table"]) for r in
                dw.tg.Ledger(self.path).records]

    def test_an_attempt_opened_under_another_table_closes_under_it(self):
        attempt = self.opened(STORAGE)
        self.assertEqual(dw.attempt_table(self.path, attempt), STORAGE)
        self.assertTrue(dw.end_attempt(
            self.path, self.report(attempt), self.output, False))
        self.assertEqual(self.tables(), [("open", STORAGE),
                                         ("close", STORAGE)])
        # an information run too
        info = dw.open_attempt(
            self.path, "info", table=STORAGE, mode="smoke", key="k",
            seed="s", output="o", checkout="c")
        self.assertTrue(dw.end_attempt(
            self.path, dict(attempt=info, mode="smoke", stage=None,
                            success=True), self.output, False))
        self.assertEqual(self.tables()[-2:], [("info", STORAGE),
                                              ("info-end", STORAGE)])
        self.assertEqual(
            [r["status"] for r in dw.table_lines(
                dw.tg.Ledger(self.path), STORAGE)
             if r["event"] == "close"], [dw.FAILED])

    def test_an_attempt_of_the_active_table_closes_under_it(self):
        attempt = self.opened()
        dw.end_attempt(self.path, self.report(attempt), self.output, False)
        self.assertEqual(self.tables(), [("open", "task33-loading"),
                                         ("close", "task33-loading")])
        # a table named explicitly wins; a ledger without the opening
        # falls back to the active table
        dw.end_attempt(self.path, self.report("nope"), self.output, False,
                       table=STORAGE)
        dw.end_attempt(self.path, self.report("nope2"), self.output, False)
        self.assertEqual([t for _, t in self.tables()[-2:]],
                         [STORAGE, "task33-loading"])

    def interleaved(self):
        loading_open = self.opened()
        storage_open = self.opened(STORAGE)
        dw.end_attempt(self.path, self.report(loading_open), self.output,
                       False)
        info = dw.open_attempt(
            self.path, "info", table=STORAGE, mode="pilot", key="k",
            seed="s", output="o", checkout="c")
        dw.end_attempt(self.path, self.report(storage_open), self.output,
                       False)
        dw.end_attempt(self.path, dict(attempt=info, mode="pilot",
                                       stage=None, success=True),
                       self.output, False)
        return loading_open, storage_open, info

    def test_the_loading_reads_ignore_the_storage_lines(self):
        loading_open, storage_open, info = self.interleaved()
        state, found = dw.read_ledger(self.path)
        self.assertEqual(sorted(a for a, _ in found), [loading_open])
        self.assertEqual([len(r["closes"]) for r in found.values()], [1])
        self.assertEqual(dw.info_runs(state), [])
        state, found = dw.read_ledger(self.path, STORAGE)
        self.assertEqual(sorted(a for a, _ in found), [storage_open])
        self.assertEqual([r["attempt"] for r in dw.info_runs(
            state, table=STORAGE)], [info])
        self.assertEqual(dw.attempts_table(
            found, dw.reasons(found))[0]["attempt"], storage_open)

    def test_r1_is_per_table(self):
        gate = "k"
        dw.refuse_second_draw(self.path, gate, "first")
        attempt = self.opened(STORAGE)
        dw.end_attempt(self.path, self.report(attempt), self.output, False)
        # the storage attempt closed with no seal: judged, for its table
        with self.assertRaisesRegex(dw.Refusal, "judged attempt"):
            dw.refuse_second_draw(self.path, gate, "first", STORAGE)
        dw.refuse_second_draw(self.path, gate, "first")
        dw.refuse_second_draw(self.path, gate, "first", "task99")
        other = self.opened()
        dw.end_attempt(self.path, self.report(other), self.output, False)
        with self.assertRaisesRegex(dw.Refusal, "judged attempt"):
            dw.refuse_second_draw(self.path, gate, "first")
        with self.assertRaisesRegex(dw.Refusal, "judged attempt"):
            dw.refuse_second_draw(self.path, gate, "first", STORAGE)

    def test_check_ledger_reads_the_named_table(self):
        attempt = self.opened(STORAGE)
        saved = self.output / "downstream.json"
        saved.write_text("{}\n")
        report = dict(self.report(attempt), key="k", layout_seed="s",
                      counts=None)
        self.assertTrue(dw.end_attempt(self.path, report, self.output,
                                       True))
        seal = a.seal(saved)
        got = dw.check_ledger(self.path, report, seal, dw.FAILED, STORAGE)
        self.assertEqual(got, dict(attempts=1, judged=1))
        with self.assertRaisesRegex(dw.Refusal, "no opening"):
            dw.check_ledger(self.path, report, seal, dw.FAILED)

    def test_the_storage_tool_sees_no_loading_line(self):
        self.interleaved()
        self.assertEqual(
            {r["table"] for r in dw.table_lines(
                dw.tg.Ledger(self.path), STORAGE)}, {STORAGE})
        self.assertEqual(
            {r["table"] for r in dw.table_lines(
                dw.tg.Ledger(self.path))}, {"task33-loading"})


class UnitEnvironment(Base33):
    def test_a_unit_env_key_must_be_a_probe_variable(self):
        for env in (dict(T32_STATS="x"), dict(T32_LAYOUT="1"),
                    dict(T32_BUSY="1"), dict(POLY_CLINE_OPTIONS="x"),
                    dict(PATH="/x"), {"T33_A": 1}, dict(T33_OK="1",
                                                        HOME="/h")):
            with self.assertRaisesRegex(dw.Refusal, "not T33_"):
                dw.check_unit_env(dict(name="u", env=env))
        dw.check_unit_env(dict(name="u", env=dict(T33_A="1")))
        dw.check_unit_env(dict(name="u"))

    def test_the_cases_of_a_table_are_checked_when_it_is_selected(self):
        bad = dict(cases33.UNITS[0], env=dict(T32_STATS="/x"))
        table = dataclass_replace(dw.TABLES["task33"], cases=types.
                                  SimpleNamespace(UNITS=(bad,)))
        with mock.patch.dict(dw.TABLES, task33=table):
            with self.assertRaisesRegex(dw.Refusal, "state0-empty"):
                dw.use_table("task33")

    def ctx(self):
        return dict(scratch=str(self.world.tmp))

    def test_the_driver_variables_win_over_a_unit_env(self):
        unit = dict(cases33.UNITS[0], env=dict(T33_KIND="empty"))
        env = dw.unit_env(self.ctx(), unit, "/r/T32Report.uo",
                          Path("/s.stats"), 7, None)
        self.assertEqual((env["T32_STATS"], env["T32_LAYOUT"],
                          env["T33_KIND"]), ("/s.stats", "7", "empty"))
        bad = dict(unit, env=dict(T32_STATS="/evil"))
        with self.assertRaisesRegex(dw.Refusal, "not T33_"):
            dw.unit_env(self.ctx(), bad, "/r/T32Report.uo",
                        Path("/s.stats"), 7, None)
        # even without the check the driver's values are applied last
        with mock.patch.object(dw, "check_unit_env"):
            env = dw.unit_env(self.ctx(), bad, "/r/T32Report.uo",
                              Path("/s.stats"), 7, None)
        self.assertEqual(env["T32_STATS"], "/s.stats")

    def replayed_with(self, unit_name, **change):
        report = self.smoke(names=[unit_name])
        self.assertTrue(report["success"], report.get("failure"))
        unit = dict(cases33.BY_NAME[unit_name], **change)
        with mock.patch.dict(cases33.BY_NAME, {unit_name: unit}):
            dw.replay_one(self.world.tmp / "s",
                          ledger=self.world.ledger())

    def test_replay_refuses_another_probe_environment(self):
        env = dict(cases33.BY_NAME["load-simpLib"]["env"])
        with self.assertRaisesRegex(dw.Refusal, "wrong probe environment"):
            self.replayed_with("load-simpLib", env=dict(
                env, T33_EXTRA="1"))

    def test_replay_refuses_a_missing_or_changed_probe_variable(self):
        # the receipt of a run holds T33_MODULE=simpLib
        with self.assertRaisesRegex(dw.Refusal, "wrong probe environment"):
            self.replayed_with("load-simpLib", env=dict(
                T33_KIND="load", T33_MODULE="congLib"))

    def test_replay_refuses_a_unit_with_a_driver_variable_in_its_env(self):
        env = dict(cases33.BY_NAME["state-empty"]["env"])
        with self.assertRaisesRegex(dw.Refusal, "not T33_"):
            self.replayed_with("state-empty", env=dict(
                env, T32_LAYOUT="0"))

    def test_a_table_without_env_prefix_allows_no_unit_env(self):
        self.assertIsNone(dw.TABLES["task32"].env_prefix)
        self.assertEqual(dw.TABLES["task33"].env_prefix, "T33_")
        with self.assertRaisesRegex(dw.Refusal, "not allowed|none"):
            dw.check_unit_env(dict(name="u", env=dict(T33_A="1")),
                              dw.TABLES["task32"])
        dw.check_unit_env(dict(name="u"), dw.TABLES["task32"])
        other = dataclass_replace(dw.TABLES["task33"], env_prefix="X_")
        dw.check_unit_env(dict(name="u", env=dict(X_A="1")), other)
        with self.assertRaisesRegex(dw.Refusal, "not X_"):
            dw.check_unit_env(dict(name="u", env=dict(T33_A="1")), other)

    def test_the_task32_units_have_no_env(self):
        self.assertTrue(all("env" not in u for u in t32.cases.UNITS))


class ParserAndDispatch(unittest.TestCase):
    def setUp(self):
        self.addCleanup(dw.use_table, dw.use_table("task32"))

    def test_an_abbreviated_table_option_is_refused(self):
        argv = ["--tab", "task33", "replay", "x"]
        for call in (dw.build_parser().parse_args,
                     lambda argv: dw.main(argv)):
            err = io.StringIO()
            with contextlib.redirect_stderr(err), \
                    self.assertRaises(SystemExit) as stop:
                call(argv)
            self.assertEqual(stop.exception.code, 3)
            self.assertIn("--tab", err.getvalue())
        self.assertEqual(dw.ACTIVE.name, "task32")

    def test_dispatch_refuses_a_table_that_is_not_the_active_one(self):
        args = dw.build_parser().parse_args(["recover", "--repo", "r"])
        self.assertEqual(args.table, "task32")
        with dw.using_table("task33"):
            with self.assertRaisesRegex(dw.Refusal, "--table task32"):
                dw.dispatch(args)


class LoadsClaims(Base33):
    def stats(self, loaded, before=("Lib", "Thm")):
        return dict(loaded=list(loaded), loaded_before=list(before))

    def test_every_kind_declares_what_it_loads(self):
        self.assertEqual({n: u["loads"] for n, u in
                          cases33.BY_NAME.items()}, {
            "state0-empty": (), "state-empty": (),
            "load-simpLib": ("simpLib",), "load-congLib": ("congLib",),
            "first-use": ()})

    def test_loads_problem(self):
        simp = cases33.BY_NAME["load-simpLib"]
        self.assertIsNone(dw.loads_problem(simp, self.stats(
            ["simpLib", "Traverse"])))
        self.assertRegex(dw.loads_problem(simp, self.stats([])),
                         "not newly loaded.*simpLib")
        self.assertRegex(dw.loads_problem(simp, self.stats(
            ["simpLib"], before=("Lib", "simpLib"))), "not newly loaded")
        empty = cases33.BY_NAME["state0-empty"]
        self.assertIsNone(dw.loads_problem(empty, self.stats([])))
        for name in ("simpLib", "congLib"):
            self.assertRegex(dw.loads_problem(empty, self.stats([name])),
                             "loads nothing.*" + name)
        # a module the heap already holds is not newly loaded
        first = cases33.BY_NAME["first-use"]
        self.assertIsNone(dw.loads_problem(first, self.stats(
            [], before=("Lib", "simpLib", "congLib"))))
        self.assertRegex(dw.loads_problem(first, self.stats(["congLib"])),
                         "congLib")
        # the unit of another table has no claim
        self.assertIsNone(dw.loads_problem(dict(name="u"), self.stats(
            ["simpLib"])))

    def wrapped(self, change):
        original = self.world.launch

        def launch(argv, cwd, env, timeout, out_path, fds=()):
            done = original(argv, cwd, env, timeout, out_path, fds)
            stats = json.loads(Path(env["T32_STATS"]).read_text())
            change(stats, argv)
            Path(env["T32_STATS"]).write_text(json.dumps(stats) + "\n")
            return done
        return mock.patch.object(dw, "launch", launch)

    def test_a_load_kind_that_loads_nothing_new_is_refused(self):
        def change(stats, argv):
            stats["loaded_before"] += stats["loaded"]
        with self.wrapped(change):
            report = self.smoke(names=["load-simpLib"])
        self.assertFalse(report["success"])
        self.assertRegex(report["failure"], "not newly loaded")
        self.assertFalse(report.get("blocked"))

    def test_an_empty_kind_that_loads_the_simplifier_is_refused(self):
        def change(stats, argv):
            stats["loaded"].append("simpLib")
        with self.wrapped(change):
            report = self.smoke(names=["state0-empty"])
        self.assertFalse(report["success"])
        self.assertRegex(report["failure"], "loads nothing.*simpLib")

    def test_first_use_that_newly_loads_congLib_is_a_finding(self):
        def change(stats, argv):
            if str(self.world.roots["cand"]) in argv[0]:
                stats["loaded"].append("congLib")
        with self.wrapped(change):
            report = self.smoke(names=["first-use"])
        self.assertFalse(report["success"])
        self.assertTrue(report.get("blocked"))
        self.assertRegex(report["failure"], "loads nothing.*congLib")

    def test_the_smoke_facts_show_the_claims(self):
        report = self.smoke()
        self.assertTrue(report["success"], report.get("failure"))
        units = report["outcome"]["probe"]["units"]
        self.assertTrue(all(f["loads_ok"] for found in units.values()
                            for f in found.values()))
        receipts = [a.load(self.world.tmp / "s" / r["receipt"])
                    for r in report["runs"]]
        self.assertTrue(dw.probe_facts(report, receipts)["ok"])
        for r in receipts:
            if r["workload"] == "load-simpLib" and r["side"] == "cand":
                r["stats"]["loaded"].remove("simpLib")
        facts = dw.probe_facts(report, receipts)
        self.assertFalse(facts["ok"])
        self.assertFalse(facts["units"]["load-simpLib"]["cand"]["loads_ok"])
        self.assertTrue(facts["units"]["load-simpLib"]["base"]["loads_ok"])


class CrossSideInconsistency(unittest.TestCase):
    ROOTS = dict(base="/b", cand="/c")

    def receipt(self, side, loaded, workload="u"):
        root = self.ROOTS[side]
        return dict(workload=workload, side=side, stats=dict(
            loaded_before=["Lib"], loaded=list(loaded),
            files=[[m + ".sml", root + "/src"] for m in loaded]))

    def check(self, base, cand):
        receipts = [self.receipt("base", x) for x in base] + [
            self.receipt("cand", x) for x in cand]
        report = dict(roots=self.ROOTS, reporter=dict(
            base=dict(dir="/p/b"), cand=dict(dir="/p/c")))
        dw.check_cross_side(report, receipts)

    def setUp(self):
        self.addCleanup(dw.use_table, dw.use_table("task33"))

    def test_consistent_equal_sides_pass(self):
        self.check([["A"], ["A"]], [["A"], ["A"]])

    def test_a_candidate_that_differs_from_itself_is_a_finding(self):
        with self.assertRaises(dw.Blocked) as caught:
            self.check([["A"], ["A"]], [["A"], ["B"]])
        self.assertRegex(str(caught.exception), "candidate's processes")

    def test_a_baseline_that_differs_from_itself_is_a_refusal(self):
        for cand in ([["A"], ["A"]], [["A"], ["B"]]):
            with self.assertRaises(dw.Refusal) as caught:
                self.check([["A"], ["B"]], cand)
            self.assertNotIsInstance(caught.exception, dw.Blocked)
            self.assertRegex(str(caught.exception), "on the base")

    def test_a_baseline_fault_outranks_a_candidate_finding_elsewhere(self):
        receipts = [self.receipt("base", ["A"], "u1"),
                    self.receipt("cand", ["A"], "u1"),
                    self.receipt("cand", ["B"], "u1"),
                    self.receipt("base", ["A"], "u2"),
                    self.receipt("base", ["B"], "u2")]
        report = dict(roots=self.ROOTS, reporter=dict(
            base=dict(dir="/p/b"), cand=dict(dir="/p/c")))
        with self.assertRaises(dw.Refusal) as caught:
            dw.check_cross_side(report, receipts)
        self.assertNotIsInstance(caught.exception, dw.Blocked)

    def test_a_candidate_without_a_baseline_to_compare_is_a_refusal(self):
        receipts = [self.receipt("cand", ["A"]), self.receipt("cand",
                                                              ["B"])]
        report = dict(roots=self.ROOTS, reporter=dict(
            cand=dict(dir="/p/c")))
        with self.assertRaises(dw.Refusal) as caught:
            dw.check_cross_side(report, receipts)
        self.assertNotIsInstance(caught.exception, dw.Blocked)

    def test_a_different_candidate_view_is_still_blocked(self):
        with self.assertRaises(dw.Blocked):
            self.check([["A"], ["A"]], [["B"], ["B"]])

    def test_the_preloaded_map_is_compared_by_loaded_before_names_only(
            self):
        view = dw.masked_view(self.receipt("base", ["A"]), "/b", "/p/b")
        self.assertEqual(sorted(view), ["files", "loaded", "loaded_before"])
        doc = " ".join(dw.Table.__doc__.split())
        self.assertIn("compared only through the `loaded_before` names",
                      doc)
        self.assertIn("`registry` case owes the comparison of the full "
                      "map", doc)


class PendingJournals(Base33):
    def pending(self, table):
        folder = self.world.repo / dw.TABLES[table].journals / "old"
        folder.mkdir(parents=True)
        (folder / "journal.json").write_text(json.dumps(dict(
            schema=dw.JOURNAL_SCHEMA, attempt="old", pending=dict(x=1))))
        return folder

    def test_a_pending_journal_of_either_table_blocks_a_run(self):
        for table in ("task32", "task33"):
            folder = self.pending(table)
            self.assertEqual(
                dw.pending_everywhere(self.world.repo),
                [(table, folder)])
            args, spec = self.world.info("p-" + table, "smoke")
            with self.assertRaisesRegex(dw.Refusal, "journal is pending.*"
                                        + table):
                dw.run_stage(args, spec)
            self.assertFalse((self.world.tmp / ("p-" + table)).exists())
            (folder / "journal.json").unlink()
        self.assertEqual(dw.pending_everywhere(self.world.repo), [])
        self.assertTrue(self.smoke("clean")["success"])

    def test_the_same_pending_journals_are_seen_under_each_table(self):
        self.pending("task32")
        self.pending("task33")
        for table in ("task32", "task33"):
            with dw.using_table(table):
                self.assertEqual(
                    [t for t, _ in dw.pending_everywhere(
                        self.world.repo)], ["task32", "task33"])
                self.assertEqual(len(dw.pending_journals(
                    self.world.repo)), 1)


class Digest33(unittest.TestCase):
    """`task33_cases.digest`, the digest of the task33 table."""

    def output(self, unit, root, probe_dir, **kw):
        return World33.output(cases33.BY_NAME[unit], root, probe_dir, **kw)

    def digest(self, name, text, root, probe_dir):
        return cases33.digest(text, root, probe_dir,
                              cases33.BY_NAME[name])

    def test_it_masks_the_root_and_the_probe_directory(self):
        one = self.output("load-simpLib", "/s/base", "/s/probe-base")
        two = self.output("load-simpLib", "/s/cand", "/s/probe-cand")
        self.assertNotEqual(one, two)
        self.assertEqual(
            self.digest("load-simpLib", one, "/s/base", "/s/probe-base"),
            self.digest("load-simpLib", two, "/s/cand", "/s/probe-cand"))

    def test_it_depends_on_the_evidence_not_on_timing_or_noise(self):
        base = self.output("first-use", "/s/b", "/s/p")
        again = base.replace('"cpu": 1e-05', '"cpu": 3e-05')
        self.assertNotEqual(base, again)
        self.assertEqual(self.digest("first-use", base, "/s/b", "/s/p"),
                         self.digest("first-use", again, "/s/b", "/s/p"))
        other = self.output("first-use", "/s/b", "/s/p", differ=True)
        self.assertNotEqual(self.digest("first-use", base, "/s/b", "/s/p"),
                            self.digest("first-use", other, "/s/b", "/s/p"))

    def test_the_empty_kinds_have_the_digest_of_no_checks(self):
        out = self.output("state0-empty", "/s/b", "/s/p")
        self.assertEqual(self.digest("state0-empty", out, "/s/b", "/s/p"),
                         dw.sha(b""))

    def test_it_refuses_what_is_not_the_units_process(self):
        out = self.output("load-simpLib", "/s/b", "/s/p")
        for name, text, why in (
                ("load-congLib", out, "are of load/load-simpLib"),
                ("load-simpLib", out.replace("/s/b/src", "/s/b2/src"),
                 "misplaced"),
                ("load-simpLib", "banner\n", "probe header"),
                ("load-simpLib", out + "@@T33\t{oops\n", "bad JSON")):
            with self.assertRaisesRegex(ValueError, why):
                self.digest(name, text, "/s/b", "/s/p")
        short = dict(cases33.BY_NAME["load-simpLib"], min_checks=2)
        with self.assertRaisesRegex(ValueError, "1 check record"):
            cases33.digest(out, "/s/b", "/s/p", short)

    def test_a_refusing_digest_is_a_refusal_of_the_driver(self):
        with dw.using_table("task33"):
            with self.assertRaisesRegex(dw.Refusal, "the probe's output"):
                dw.probe_digest("@@T33\t{oops\n", "/s/b", "/s/p",
                                cases33.BY_NAME["load-simpLib"])
        with dw.using_table("task32"):
            with self.assertRaisesRegex(dw.Refusal, "no probe units"):
                dw.probe_digest("", "/s/b", "/s/p", {})


class ProbeSourcesInReports(Base33):
    def test_a_run_records_the_sealed_probe_sources_and_replay_checks_them(
            self):
        report = self.smoke(names=["state-empty"])
        code = report["code"]
        for rel in cases33.PROBE_FILES + ("task33_records.py",):
            self.assertIn(rel, code)
        for side in ("base", "cand"):
            self.assertEqual(report["probes"][side]["sources"], {
                Path(rel).name: code[rel]["sha256"]
                for rel in cases33.PROBE_FILES})
        dw.check_probe_sources(report)
        for change, why in (
                (lambda r: r["probes"]["cand"]["sources"].update(
                    {"T33.sml": "0" * 64}), "cand probes"),
                (lambda r: r["probes"]["base"]["sources"].pop(
                    "T33.sml"), "base probes"),
                (lambda r: r["probes"]["base"].update(modules=["Nope"]),
                 "base probe modules"),
                (lambda r: r["probes"].pop("cand"), "cand probes"),
                (lambda r: r.pop("probes"), "base probes")):
            bad = json.loads(json.dumps(report))
            change(bad)
            with self.assertRaisesRegex(dw.Refusal, why):
                dw.check_probe_sources(bad)
        with dw.using_table("task32"):
            dw.check_probe_sources({})  # no probe units: nothing to check


class ProcessEnvironment(Base33):
    def test_the_locale_is_pinned_whatever_the_callers_is(self):
        dirty = dict(LANG="de_DE.UTF-8", LC_ALL="fr_FR", LC_CTYPE="x",
                     LC_COLLATE="y", LANGUAGE="z", HOLDIR="/elsewhere",
                     POLY_CLINE_OPTIONS="--x", T33_LEAK="1")
        with mock.patch.dict(os.environ, dirty):
            env = dw.process_env(self.world.tmp, {})
            unit = cases33.BY_NAME["first-use"]
            ctx = dict(scratch=str(self.world.tmp))
            probe = dw.unit_env(ctx, unit, "/r/T32Report.uo",
                                self.world.tmp / "s", 0, None)
        self.assertEqual(env["LC_ALL"], "C")
        self.assertEqual(probe["LC_ALL"], "C")
        for name in dirty:
            if name != "LC_ALL":
                self.assertNotIn(name, probe, name)
        self.assertFalse([k for k in probe
                          if k.startswith("LC_") and k != "LC_ALL"])
        self.assertEqual(
            {k: v for k, v in probe.items()
             if not k.startswith("T3")},
            dw.snap.environment(Path(self.world.tmp) / "home",
                                Path(self.world.tmp) / "tmp"))

    def test_task32_has_the_same_environment_as_before_the_tables(self):
        with dw.using_table("task32"):
            env = dw.process_env(self.world.tmp, {})
        self.assertEqual(env, dw.snap.environment(
            Path(self.world.tmp) / "home", Path(self.world.tmp) / "tmp"))
        self.assertEqual(env["LC_ALL"], "C")


class Controls33(unittest.TestCase):
    """A control is a separate unit; the validator's expected set comes
    from the unit's environment."""

    def test_the_ordinary_units_have_no_controls(self):
        for unit in cases33.UNITS:
            self.assertEqual(cases33.controls_of(unit), ())

    def test_a_control_unit_sets_one_switch_in_its_own_environment(self):
        base = dict(cases33.BY_NAME["load-simpLib"], probe="T33Registry")
        unit = cases33.control_unit(base, "hook")
        self.assertEqual(unit["name"], "load-simpLib+hook")
        self.assertEqual(unit["env"], dict(base["env"], T33_HOOK="1"))
        self.assertEqual(cases33.controls_of(unit), ("hook",))
        self.assertEqual(base["env"], cases33.BY_NAME[
            "load-simpLib"]["env"])
        dw.check_unit_env(unit, dw.TABLES["task33"])  # T33_* only
        for switch, name in (("leak", "T33_LEAK"),
                             ("graph_extra", "T33_GRAPH_EXTRA")):
            probe = dict(base, probe="T33Release" if switch == "leak"
                         else "T33Graph")
            got = cases33.control_unit(probe, switch)
            self.assertEqual(got["env"][name], "1")

    def test_a_control_must_act_in_the_units_probe(self):
        timed = cases33.BY_NAME["load-simpLib"]
        for switch in ("hook", "leak", "graph_extra"):
            with self.assertRaisesRegex(ValueError, "inert"):
                cases33.control_unit(timed, switch)
        with self.assertRaisesRegex(ValueError, "inert"):
            cases33.control_unit(dict(timed, probe="T33Registry"), "leak")
        with self.assertRaisesRegex(ValueError, "inert"):
            cases33.control_unit(timed, "nonsense")

    def test_a_bad_switch_value_is_refused(self):
        unit = dict(cases33.BY_NAME["load-simpLib"], env=dict(
            T33_KIND="x", T33_LEAK="yes"))
        with self.assertRaisesRegex(ValueError, "not 0 or 1"):
            cases33.controls_of(unit)

    def test_the_digest_requires_the_controls_the_unit_declares(self):
        reg = dict(cases33.BY_NAME["state0-empty"], probe="T33Registry")
        hook = cases33.control_unit(reg, "hook")
        run = rt.load_run("registry", "state0-empty", hook=True)
        for record in run:
            if record["record"] == "probe":
                record["holdir"] = "/s/b"
        text = rt.text(run)
        cases33.digest(text, "/s/b", "/s/p", hook)
        with self.assertRaisesRegex(ValueError, "control switches"):
            cases33.digest(text, "/s/b", "/s/p", reg)


class Messages(Base33):
    def test_a_stale_code_seal_names_the_active_tables_history(self):
        seals = dw.code_seals()
        bad = dict(seals, **{"task33_cases.py": dict(
            seals["task33_cases.py"], sha256="0" * 64)})
        with self.assertRaisesRegex(dw.Refusal, "HISTORY of table task33"):
            dw.check_code(bad)
        with dw.using_table("task32"):
            with self.assertRaisesRegex(dw.Refusal,
                                        "HISTORY of table task32"):
                dw.check_code(dict(dw.code_seals(), **{
                    "task32_cases.py": dict(
                        dw.code_seals()["task32_cases.py"],
                        sha256="0" * 64)}))

    def test_a_probe_directory_churn_is_not_called_a_snapshot_one(self):
        self.world.fault = lambda unit, side, n: "churn"
        report = self.smoke(names=["load-simpLib"])
        self.assertRegex(report["failure"], "probe directory")


class Chain33(Base33):
    """smoke -> pilot -> control -> predeclare -> first stage -> replay of
    the chain, under the task33 table, on fake processes."""

    def test_predeclare_run_and_replay_chain(self):
        w = self.world
        ledger = w.ledger()
        perf = w.repo / "src/simp/tests/performance"
        for mode, extra in (("smoke", {}), ("pilot", {}),
                            ("control", dict(pilot=w.tmp / "pilot"))):
            args, spec = w.info(mode, mode, **extra)
            run = dw.run_stage(args, spec)
            self.assertTrue(run["success"], run.get("failure"))
            self.assertEqual(run["table"], "task33")
        pilot = a.load(w.tmp / "pilot" / "downstream.json")
        want = {n: p["reps"] for n, p in
                pilot["outcome"]["pilot"].items()}
        # the floor of one second of CPU: 0.25 s units get at least 4
        self.assertGreaterEqual(want["state0-empty"], 4)
        self.assertGreaterEqual(want["load-simpLib"], 2)
        counts = dw.predeclare_first(w.args(
            "x", pilot=w.tmp / "pilot", smoke=w.tmp / "smoke",
            control=w.tmp / "control"))
        self.assertEqual(counts["table"], "task33")
        self.assertEqual(counts["r_cap"], 8)
        self.assertEqual(counts["seed"], "task33-1")
        self.assertEqual(counts["reps"], want)
        self.assertEqual(counts["capped"], [])
        self.assertEqual(sorted(counts["references"]),
                         sorted(cases33.NAMES))
        counts_path = perf / "counts.json"
        counts_path.write_text(dw.dumps(counts))
        t32.git(w.repo, "add", os.path.relpath(counts_path, w.repo))
        t32.git(w.repo, "commit", "-q", "-m", "counts")
        args = w.args("first", counts=counts_path)
        spec = dw.first_spec(args)
        self.assertEqual(spec["names"], list(cases33.NAMES))
        self.assertEqual(spec["reps"], counts["reps"])
        self.assertEqual(spec["seed"], "task33-1")
        first = dw.run_stage(args, spec)
        self.assertTrue(first["success"], first.get("failure"))
        self.assertEqual(first["table"], "task33")
        self.assertEqual(len(first["runs"]), 20 * 4 * sum(
            counts["reps"].values()))
        found = dw.read_ledger(ledger)[1]
        self.assertEqual({r["opens"][0]["table"] for r in found.values()
                          if r["opens"][0]["stage"] == "first"},
                         {"task33-loading"})
        chain = dw.replay_chain(w.tmp / "first", ledger,
                                counts=counts_path, repo=w.repo)
        self.assertEqual([e["stage"] for e in chain], ["first"])
        dw.check_counts_use(first, counts_path, w.repo)
        # a counts file of the other table is not the run's
        other = dict(counts)
        other.pop("table")
        other_path = perf / "other.json"
        other_path.write_text(dw.dumps(other))
        with self.assertRaises(dw.Refusal):
            dw.check_counts_use(first, other_path, w.repo)
        with dw.using_table("task32"):
            with self.assertRaisesRegex(dw.Refusal, "of table task33"):
                dw.replay_chain(w.tmp / "first", ledger,
                                counts=counts_path, repo=w.repo)
        # a second draw of the gate needs a policy decision
        with self.assertRaisesRegex(dw.Refusal, "judged attempt"):
            dw.run_stage(w.args("again", counts=counts_path), spec)


class ShortKindChain33(Base33):
    """A kind of about 0.07 s per process: pilot, exit, replay, control and
    predeclare, with R declared at the cap."""

    def test_a_short_startup_kind_is_covered_by_its_sample(self):
        w = self.world
        ledger = w.ledger()
        unit = cases33.BY_NAME["state0-empty"]
        with mock.patch.dict(unit, serial=0.07):
            args, spec = w.info("pilot", "pilot")
            pilot = dw.run_stage(args, spec)
            self.assertTrue(pilot["success"], pilot.get("failure"))
            self.assertEqual(dw.exit_of(pilot), 0)
            found = pilot["outcome"]["pilot"]["state0-empty"]
            self.assertAlmostEqual(found["median_cpu"], 0.07, places=2)
            self.assertLess(found["median_cpu"], dw.MIN_UNIT_CPU)
            self.assertGreater(found["reps"], dw.R_CAP)
            self.assertAlmostEqual(found["floor_cpu"], 0.56, places=1)
            self.assertTrue(pilot["outcome"]["covered"])
            # replay_one recomputes the outcome (floor_cpu included) from
            # the receipts and raises on a mismatch: not raising is the
            # check
            dw.replay_one(w.tmp / "pilot", ledger=ledger)
            for mode, extra in (("smoke", {}),
                                ("control", dict(pilot=w.tmp / "pilot"))):
                args, spec = w.info(mode, mode, **extra)
                run = dw.run_stage(args, spec)
                self.assertTrue(run["success"], run.get("failure"))
            counts = dw.predeclare_first(w.args(
                "x", pilot=w.tmp / "pilot", smoke=w.tmp / "smoke",
                control=w.tmp / "control"))
            self.assertIn("state0-empty", counts["capped"])
            self.assertEqual(counts["reps"]["state0-empty"], dw.R_CAP)
            self.assertGreater(counts["required_reps"]["state0-empty"],
                               dw.R_CAP)


class Task32Unchanged(Base):
    def test_a_task32_report_has_no_table_key_and_replays_under_task32(
            self):
        self.world.profile["logroot"] = (1.05, 0.001)
        report = self.world.run("r", self.world.spec(["logroot"]))
        self.assertTrue(report["success"], report.get("failure"))
        self.assertNotIn("table", report)
        self.assertNotIn("probes", report)
        self.assertEqual(report["claims"], "NOT release acceptance: "
                         "proof-build timing only")
        self.assertEqual(report["layout_seed"], "task32-1")
        info, again = dw.replay_one(self.world.tmp / "r",
                                    ledger=self.world.ledger())
        self.assertEqual(dw.dumps(again), dw.dumps(report))
        with dw.using_table("task33"):
            with self.assertRaisesRegex(dw.Refusal, "of table task32"):
                dw.replay_one(self.world.tmp / "r",
                              ledger=self.world.ledger())
        self.assertEqual(dw.ACTIVE.name, "task32")

if __name__ == "__main__":
    unittest.main()
