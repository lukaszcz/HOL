#!/usr/bin/env python3
"""TASK32 proof-build timing driver (task32_downstream.py), on fake trees and
fake processes: synthetic rows, refusals, restore, schedule, counts commit
rules, replay, and a whole smoke -> pilot -> counts -> first stage -> second
stage -> follow-up -> disposition chain."""
import argparse
import gzip
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import acceptance as a
import loading
import task32_cases as cases
import task32_downstream as dw

_cache = {}
_real_statistics = a.paired_statistics


def cached_statistics(observations, margin=0.0, gated=True):
    """The bootstrap is deterministic: compute each distinct input once."""
    key = json.dumps([observations, margin, gated], sort_keys=True)
    if key not in _cache:
        _cache[key] = _real_statistics(observations, margin, gated)
    return json.loads(json.dumps(_cache[key]))


def setUpModule():
    patcher = mock.patch.object(a, "paired_statistics", cached_statistics)
    patcher.start()
    unittest.addModuleCleanup(patcher.stop)


def git(repo, *args):
    return subprocess.run(
        ["git", "-C", str(repo), "-c", "user.name=t", "-c",
         "user.email=t@t", *args], check=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, text=True).stdout.strip()


STAT_FIELDS = dict(gc_full=1, gc_partial=3, gc_share=0, size_heap=1 << 20)


class World:
    """Two fake snapshots with the 15 units' directories and prebuilt
    products, a git repository for the ledger and the counts commits, and a
    fake `launch` that plays the processes."""

    def __init__(self, tmp):
        self.tmp = Path(tmp)
        self.repo = self.tmp / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q")
        (self.repo / ".gitignore").write_text(".agent-files/\n")
        perf = self.repo / "src/simp/tests/performance"
        perf.mkdir(parents=True)
        (perf / "keep").write_text("x\n")
        (self.repo / "compiled.sml").write_text("val x = 1\n")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "init")
        self.cand_pin = git(self.repo, "rev-parse", "HEAD")
        self.base_pin = "1" * 40
        self.roots = {"base": self.tmp / "base", "cand": self.tmp / "cand"}
        for side, root in self.roots.items():
            self.build_tree(side, root)
        self.manifest = self.tmp / "snapshots.json"
        self.manifest.write_text(json.dumps({
            "schema": "task32-independent-build-v2",
            "sides": {s: dict(root=str(r), pin=pin, tree=pin)
                      for (s, r), pin in zip(
                          self.roots.items(),
                          (self.base_pin, self.cand_pin))}}))
        self.profile = {}  # workload -> (candidate scale, noise)
        self.default = (1.0, 0.001)
        self.counter = 0
        self.fault = None  # (unit, side, n) -> kind or None
        self.calls = []

    def build_tree(self, side, root):
        (root / "bin").mkdir(parents=True)
        for n in ("Holmake", "hol", "hol.state0"):
            (root / "bin" / n).write_text("x")
        (root / "sigobj").mkdir()
        (root / "sigobj/Lib.ui").symlink_to(root / "bin/hol")
        for unit in cases.UNITS:
            folder = root / unit["dir"]
            (folder / ".hol/objs").mkdir(parents=True, exist_ok=True)
            (folder / ".hol/docs").mkdir(parents=True, exist_ok=True)
            (folder / ".hol/logs").mkdir(parents=True, exist_ok=True)
            if unit["kind"] == "theory":
                self.write_products(folder, unit["theory"], root, "sig")
            else:
                (folder / "selftest.exe").write_text(
                    "#!/bin/sh\nset -e\n%s/bin/hol --gcthreads=1 run "
                    "--holstate=%s  selftest\nexit 0\n" % (
                        root, root / unit["heap"]))
            (folder / "other.sml").write_text("val x = 1\n")
            os.utime(folder / "other.sml", ns=(10 ** 18, 10 ** 18))

    @staticmethod
    def write_products(folder, name, root, sig):
        for ext in ("sig", "dat", "uo", "ui", "sml", "cachekey"):
            path = folder / ".hol/objs" / ("%sTheory.%s" % (name, ext))
            path.write_text("%s %s %s\n" % (
                sig if ext == "sig" else ext, name, root))
            os.utime(path, ns=(2 * 10 ** 18, 2 * 10 ** 18))
        (folder / ".hol/docs" / ("%sTheory.html" % name)).write_text("h\n")

    def snapshot(self):
        return {s: dw.scan(r) for s, r in self.roots.items()}

    # the fake processes ------------------------------------------------
    def launch(self, argv, cwd, env, timeout, out_path, fds=()):
        side = "cand" if str(self.roots["cand"]) in argv[0] else "base"
        root = self.roots[side]
        cwd = Path(cwd)
        theory = Path(argv[-1]).name.endswith("Theory.uo")
        unit = None
        for u in cases.UNITS:
            if root / u["dir"] == cwd and (
                    (u["kind"] == "theory" and theory and
                     argv[-1] == "%sTheory.uo" % u["theory"]) or
                    (u["kind"] == "selftest" and not theory)):
                unit = u
        assert unit is not None, (argv, cwd)
        self.counter += 1
        self.calls.append((unit["name"], side, dict(env)))
        scale, noise = self.profile.get(unit["name"], self.default)
        rng = random.Random(self.counter)
        factor = (scale if side == "cand" else 1.0) * (
            1 + noise * rng.uniform(-1, 1))
        if "T32_BUSY" in env:
            factor *= 1 + float(env["T32_BUSY"])
        cpu = unit["serial"] * factor
        fault = self.fault and self.fault(unit, side, self.counter)
        stats = dict(schema=dw.STATS_SCHEMA, nongc_usr=cpu * 0.9,
                     nongc_sys=cpu * 0.05, gc_usr=cpu * 0.04,
                     gc_sys=cpu * 0.01, gc_time=cpu * 0.05 * (
                         1 + 0.2 * rng.random()), holdir=str(root),
                     loaded_before=["Lib", "Thm"], loaded=["Foo"],
                     files=[["Foo.sml", str(root / "src/foo")]],
                     **STAT_FIELDS)
        if theory:
            folder = cwd
            sig = "bad" if fault == "mismatch" else "sig"
            self.write_products(folder, unit["theory"], root, sig)
            if fault == "stray":
                (folder / "stray.txt").write_text("x")
            out = "Holmake: built %s in %.2fs\n" % (unit["name"],
                                                    rng.random())
        else:
            out = "selftest ok (%.1fs)\n" % rng.uniform(1, 5)
            if fault == "mismatch":
                out += "different\n"
            if fault == "stray":
                (cwd / "stray.txt").write_text("x")
        if fault == "extension":
            stats["loaded"].append("simpExt")
        if fault == "outside":
            stats["files"].append(["Bar.sml", "/elsewhere"])
        if fault == "holdir":
            stats["holdir"] = "/elsewhere"
        Path(out_path).write_text(out)
        if fault != "nostats":
            Path(env["T32_STATS"]).write_text(json.dumps(stats) + "\n")
        return dict(exit=1 if fault == "exit" else 0, timed_out=False,
                    wall=cpu * 1.03, utime=cpu * 0.9, stime=cpu * 0.1,
                    maxrss=10 ** 8)

    @staticmethod
    def reporter(root, folder, env, timeout, fds):
        folder = Path(folder)
        folder.mkdir(parents=True)
        (folder / "T32Report.uo").write_text("x")
        return dict(dir=str(folder), uo=str(folder / "T32Report.uo"),
                    source_sha256=dw.REPORTER_SEAL,
                    build_stdout_sha256="0" * 64)

    def patches(self):
        return [
            mock.patch.object(dw, "launch", self.launch),
            mock.patch.object(dw, "build_reporter", self.reporter),
            mock.patch.object(dw, "check_candidate", lambda r, s: "c31"),
            mock.patch.object(dw, "poly_version",
                              lambda env, cwd, fds: "Poly/ML fake")]

    def args(self, name, **extra):
        values = dict(
            repo=self.repo, base_root=self.roots["base"],
            cand_root=self.roots["cand"], manifest=self.manifest,
            ledger=None, counts=None, output=self.tmp / name,
            scratch=self.tmp / "scratch", timeout=60,
            verify_argv=[sys.executable, "-c", "pass"], no_verify=False,
            authorize_measurements=True, only=[], reps=1,
            followup_counts=None)
        values.update(extra)
        return argparse.Namespace(**values)

    def spec(self, names, pairs=10, stage="first", seed=None, reps=1):
        return dict(mode=stage, stage=stage, names=names,
                    pairs={w: pairs for w in names},
                    reps={w: reps for w in names},
                    seed=seed or dw.SEEDS[stage], references=None)

    def run(self, name, spec, **extra):
        return dw.run_stage(self.args(name, **extra), spec)

    def status(self):
        found = dw.read_ledger(dw.ledger_path(self.repo))[1]
        return [(k, [c["status"] for c in r["closes"]])
                for k, r in found.items()]


class Base(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory(prefix="t32-test-")
        self.addCleanup(self.dir.cleanup)
        self.world = World(self.dir.name)
        for patch in self.world.patches():
            patch.start()
            self.addCleanup(patch.stop)
        self.addCleanup(self.remove_lock)

    def remove_lock(self):
        for lock in Path(self.world.repo, ".agent-files").glob("*.lock"):
            lock.unlink()


def rows(base, cand, pairs=20, reps=1):
    """Synthetic admitted rows of one phase pair: per process measured
    values given as functions of the pair index."""
    out = []
    for i, side, r in loading.schedule(pairs, reps):
        value = base(i) if side == "baseline" else cand(i)
        out.append(dict(pair=i, selection=side, rep=r, accepted=True,
                        measurement=dict(raw=dict(
                            cpu=value, wall=value * 1.02,
                            gc_cpu=value * 0.05, maxrss=1e8))))
    return out


class Statistics(unittest.TestCase):
    def jitter(self, i):
        return 1 + 0.002 * ((i * 7) % 5 - 2)

    def result(self, scale, control_scale=1.0, pairs=20):
        control = rows(lambda i: 5 * self.jitter(i),
                       lambda i: 5 * control_scale * self.jitter(i + 1),
                       pairs)
        cand = rows(lambda i: 5 * self.jitter(i),
                    lambda i: 5 * scale * self.jitter(i + 2), pairs)
        return dw.analyze(control, cand, pairs, 1)

    def test_a_five_percent_slowdown_fails(self):
        res = self.result(1.05)
        self.assertEqual(res["decision"], "fail")
        self.assertTrue(res["control_valid"])
        for metric in ("cpu", "wall"):
            self.assertEqual(res["candidate"]["metrics"][metric]["decision"],
                             "fail")

    def test_equal_candidates_pass_and_gc_is_only_reported(self):
        res = self.result(1.0)
        self.assertEqual(res["decision"], "pass")
        for metric in ("gc_cpu", "maxrss"):
            data = res["candidate"]["metrics"][metric]
            self.assertEqual(data["decision"], "reported")
            self.assertFalse(data["gated"])

    def test_a_two_percent_slowdown_is_inside_the_margin(self):
        self.assertEqual(self.result(1.02)["decision"], "pass")

    def test_a_control_outside_the_window_makes_a_pass_inconclusive(self):
        res = self.result(1.0, control_scale=1.06)
        self.assertEqual(res["decision"], "inconclusive")
        self.assertFalse(res["control_valid"])
        self.assertEqual(dw.second_stage_plan({"x": res}),
                         {"x": res["second_stage_pairs"]})

    def test_a_fail_is_final_even_with_a_bad_control(self):
        res = self.result(1.2, control_scale=1.06)
        self.assertEqual(res["decision"], "fail")
        self.assertEqual(dw.second_stage_plan({"x": res}), {})

    def test_the_second_stage_count_is_the_grids_rule(self):
        res = self.result(1.0, control_scale=1.06)
        self.assertEqual(res["second_stage_pairs"],
                         loading.second_stage_count(res["control"], 20))
        self.assertGreaterEqual(res["second_stage_pairs"], 40)

    def test_statistics_refuse_a_reordered_or_rejected_schedule(self):
        good = rows(lambda i: 5.0, lambda i: 5.0)
        with self.assertRaises(dw.Refusal):
            dw.statistics(list(reversed(good)), 20, 1)
        bad = [dict(r) for r in good]
        bad[3]["accepted"] = False
        with self.assertRaises(dw.Refusal):
            dw.statistics(bad, 20, 1)

    def test_classification_table(self):
        def res(decision, valid):
            return dict(decision=decision, control_valid=valid)
        c = dw.classify
        self.assertEqual(c([("first", res("pass", True))])[0], "pass")
        self.assertEqual(c([("first", res("fail", False))])[0], "fail")
        self.assertEqual(c([("first", res("inconclusive", False))])[0],
                         "blocked")
        self.assertEqual(c([("first", res("inconclusive", True))])[0],
                         "blocked")
        chain = [("first", res("inconclusive", False)),
                 ("second", res("inconclusive", True))]
        self.assertEqual(c(chain)[0], "followup")
        self.assertEqual(c(chain[:1] + [("second",
                                         res("inconclusive", False))])[0],
                         "blocked")
        self.assertEqual(c(chain + [("followup",
                                     res("inconclusive", True))])[0],
                         "blocked")
        self.assertEqual(c(chain + [("followup", res("pass", True))])[0],
                         "pass")
        self.assertEqual(c(chain + [("followup", res("fail", True))])[0],
                         "fail")


class Schedule(unittest.TestCase):
    def test_round_robin_with_ab_ba_pairs(self):
        names = ["x", "y"]
        pairs, reps = dict(x=3, y=2), dict(x=2, y=1)
        order = dw.expected_runs(names, pairs, reps, dw.PROCESS_PHASES)
        self.assertEqual(len(order), 2 * 2 * (3 * 2 + 2 * 1))
        # round i holds every workload that still has a pair i
        self.assertEqual([o[0] for o in order if o[2] == 2], ["x"] * 8)
        rounds = [o[2] for o in order]
        self.assertEqual(rounds, sorted(rounds))
        for w in names:
            for phase in dw.PROCESS_PHASES:
                mine = [(p, s, r) for (n, ph, p, s, r) in order
                        if (n, ph) == (w, phase)]
                self.assertEqual(mine, loading.schedule(pairs[w], reps[w]))
        first = [o for o in order if o[:3] == ("x", "candidate", 0)]
        second = [o for o in order if o[:3] == ("x", "candidate", 1)]
        self.assertEqual([o[3] for o in first],
                         ["baseline", "candidate"] * 2)
        self.assertEqual([o[3] for o in second],
                         ["candidate", "baseline"] * 2)
        # the control pair of a round precedes its candidate pair
        self.assertLess(order.index(("x", "control", 0, "baseline", 0)),
                        order.index(("x", "candidate", 0, "baseline", 0)))

    def test_control_processes_run_in_the_base_snapshot(self):
        self.assertEqual(dw.side_of("control", "candidate"), "base")
        self.assertEqual(dw.side_of("candidate", "baseline"), "base")
        self.assertEqual(dw.side_of("candidate", "candidate"), "cand")
        self.assertEqual(dw.side_of("pilot", "candidate"), "base")
        self.assertEqual(dw.side_of("smoke", "candidate"), "cand")

    def test_the_layout_is_that_of_loading_and_seeded(self):
        got = dw.layout_for("task32-1", 3, "candidate", 1)
        self.assertEqual(got, loading.layout_units(
            "task32-1", "control", 3, "candidate", 1))
        self.assertNotEqual({dw.layout_for("task32-1", p, "baseline", 0)
                             for p in range(20)}, {got})
        self.assertNotEqual(
            [dw.layout_for(dw.SEEDS["first"], p, "baseline", 0)
             for p in range(20)],
            [dw.layout_for(dw.SEEDS["second"], p, "baseline", 0)
             for p in range(20)])
        self.assertEqual(len({dw.SEEDS.values()} | set()), 1)
        self.assertEqual(len(set(dw.SEEDS.values())), len(dw.SEEDS))


class Pieces(unittest.TestCase):
    good = dict(schema=dw.STATS_SCHEMA, nongc_usr=1.0, nongc_sys=0.1,
                gc_usr=0.1, gc_sys=0.0, gc_time=0.1, holdir="/r",
                loaded_before=["Lib"], loaded=["X"], files=[["X.sml", "/r/a"]],
                **STAT_FIELDS)

    def test_the_cases_are_fifteen_units_over_four_heaps(self):
        self.assertEqual(len(cases.UNITS), 15)
        self.assertEqual({u["area"] for u in cases.UNITS},
                         set(cases.AREAS))
        self.assertEqual(len(cases.HEAPS), 4)
        self.assertEqual(sum(u["kind"] == "selftest" for u in cases.UNITS),
                         5)
        self.assertEqual(len(cases.NAMES), len(set(cases.NAMES)))

    def test_the_reporter_is_sealed_and_uses_the_probed_interfaces(self):
        text = dw.REPORTER
        for needle in ("OS.Process.atExit", "T32_STATS", "T32_LAYOUT",
                       "T32_BUSY", "getLocalStats", "gcFullGCs",
                       "gcPartialGCs", "sizeHeap", "checkGCTime",
                       "Systeml.HOLDIR", "Meta.fileDirMap"):
            self.assertIn(needle, text)
        self.assertEqual(dw.REPORTER_SEAL,
                         dw.hashlib.sha256(text.encode()).hexdigest())
        self.assertFalse(any(len(x) > 79 for x in text.splitlines()))

    def test_stats_parsing_refuses_missing_or_malformed_lines(self):
        line = json.dumps(self.good)
        self.assertEqual(dw.parse_stats(line + "\n")["holdir"], "/r")
        for text in ("", "\n", line + "\n" + line + "\n", "{oops",
                     json.dumps(dict(self.good, schema="x")),
                     json.dumps(dict(self.good, gc_time=-1)),
                     json.dumps(dict(self.good, gc_full="1")),
                     json.dumps(dict(self.good, files=[["a"]]))):
            with self.assertRaises(dw.Refusal, msg=text):
                dw.parse_stats(text)

    def test_loaded_paths_must_be_inside_the_root_and_not_extensions(self):
        root = Path("/r")
        dw.check_loaded(self.good, root, "/rep", False)
        for change in (dict(holdir="/s"),
                       dict(files=[["X.sml", "/elsewhere"]]),
                       dict(loaded=["fooExt"]),
                       dict(loaded_before=["simpExt"]),
                       dict(files=[["simpMarker.sml", "/r/a"]])):
            with self.assertRaises(dw.Refusal):
                dw.check_loaded(dict(self.good, **change), root, "/rep",
                                False)
        dw.check_loaded(dict(self.good, files=[["T32Report.sml", "/rep"]]),
                        root, "/rep", False)
        with self.assertRaises(dw.Blocked):
            dw.check_loaded(dict(self.good, loaded=["fooExt"]), root,
                            "/rep", True)

    def test_normalization_masks_root_durations_and_colour(self):
        text = "\x1b[1mok\x1b[0m /r/x took 12.5s and 3 ms (4s)\n"
        self.assertEqual(dw.normalize_text(text, "/r"),
                         "ok $(HOLDIR)/x took <T> and 3 ms (<T>)\n".replace(
                             "3 ms", "<T>"))

    def test_theory_digest_masks_the_root_and_needs_both_files(self):
        one = dw.theory_digest(dict(sig=b"a /r1 b", dat=b"/r1"), "/r1")
        two = dw.theory_digest(dict(sig=b"a /r2 b", dat=b"/r2"), "/r2")
        self.assertEqual(one, two)
        with self.assertRaises(dw.Refusal):
            dw.theory_digest(dict(sig=b"a"), "/r1")

    def test_selftest_exe_format_is_checked(self):
        root = Path("/r")
        unit = cases.BY_NAME["arith-selftest"]
        text = ("#!/bin/sh\nset -e\n/r/bin/hol --gcthreads=1 run "
                "--holstate=/r/bin/hol.state0  selftest\nexit 0\n")
        self.assertEqual(dw.parse_selftest(text, root, unit)[-1], "selftest")
        for bad in (text.replace("/r/bin/hol.state0", "/q/bin/hol.state0"),
                    text.replace("/r/bin/hol ", "/q/bin/hol "),
                    text.replace("set -e\n", ""),
                    text.replace("--gcthreads=1", "--gcthreads=2")):
            with self.assertRaises(dw.Refusal):
                dw.parse_selftest(bad, root, unit)

    def test_product_pattern_covers_exactly_the_target(self):
        entries = {p: ["f", 1, 1, "x"] for p in (
            ".hol/objs/ratTheory.dat", ".hol/objs/ratTheory.uo",
            ".hol/docs/ratTheory.html", ".hol/docs/ratScript.html",
            ".hol/objs/ratScript.uo", ".hol/objs/integerTheory.dat",
            ".hol/objs/rat_xTheory.dat", ".hol/objs/ratTheory.dat.bak",
            "ratTheory.sig")}
        self.assertEqual(dw.products(entries, "rat"), [
            ".hol/docs/ratScript.html", ".hol/docs/ratTheory.html",
            ".hol/objs/ratTheory.dat", ".hol/objs/ratTheory.uo",
            "ratTheory.sig"])

    def test_scan_restore_round_trip_keeps_bytes_and_mtimes(self):
        with tempfile.TemporaryDirectory() as tmp:
            folder, store = Path(tmp, "d"), Path(tmp, "s")
            (folder / ".hol/objs").mkdir(parents=True)
            (folder / ".hol/logs").mkdir()
            path = folder / ".hol/objs/xTheory.dat"
            path.write_bytes(b"abc")
            os.utime(path, ns=(5 * 10 ** 18, 5 * 10 ** 18))
            (folder / ".hol/logs/x").write_text("log")
            before = dw.scan(folder, dw.TRANSIENT)
            rels = dw.products(before, "x")
            meta = dw.back_up(folder, rels, store)
            path.unlink()
            path.write_bytes(b"new")
            (folder / ".hol/objs/xTheory.uo").write_text("extra")
            (folder / ".hol/logs/x").write_text("other log")
            now = dw.products(dw.scan(folder, dw.TRANSIENT), "x")
            self.assertNotEqual(dw.scan(folder, dw.TRANSIENT), before)
            dw.restore(folder, meta, store, now)
            self.assertEqual(dw.scan(folder, dw.TRANSIENT), before)
            self.assertEqual(path.read_bytes(), b"abc")
            self.assertEqual(path.stat().st_mtime_ns, 5 * 10 ** 18)

    def test_validate_names_each_refusal(self):
        usage = dict(exit=0, timed_out=False, wall=1.0, utime=1.0,
                     stime=0.0, maxrss=1)
        rec = dict(usage=usage, stats=self.good, stray=[], digest="d")
        unit = cases.BY_NAME["logroot"]
        dw.validate(rec, unit, Path("/r"), "/rep", "d", False)
        for change, text in (
                (dict(usage=dict(usage, exit=1)), "failed"),
                (dict(usage=dict(usage, timed_out=True)), "timed out"),
                (dict(stats=None), "missing stats"),
                (dict(stray=["a.txt"]), "stray write"),
                (dict(digest="e"), "differs")):
            with self.assertRaisesRegex(dw.Refusal, text):
                dw.validate(dict(rec, **change), unit, Path("/r"), "/rep",
                            "d", False)
        with self.assertRaises(dw.Blocked):
            dw.validate(dict(rec, digest="e"), unit, Path("/r"), "/rep",
                        "d", True)


class Refusals(Base):
    """Every per-process refusal, through the whole pipeline: the row is
    archived as rejected, the attempt closes failed (or blocked) and the
    snapshots are byte-identical afterwards."""

    def attempt(self, kind, name="logroot", side=None, at=1, stage="first"):
        self.world.fault = lambda unit, s, n: (
            kind if n >= at and unit["name"] == name and
            side in (None, s) else None)
        before = self.world.snapshot()
        report = self.world.run("out-" + kind, self.world.spec(
            [name], stage=stage))
        self.assertFalse(report["success"], kind)
        for stray in self.world.tmp.glob("*/**/stray.txt"):
            stray.unlink()  # a stray write is refused, not undone
        self.assertEqual(self.world.snapshot(), before, kind)
        self.assertFalse(report["runs"][-1]["accepted"])
        return report

    def test_a_failed_process_is_refused(self):
        report = self.attempt("exit")
        self.assertIn("process failed: exit 1", report["failure"])

    def test_missing_stats_are_refused(self):
        self.assertIn("missing stats", self.attempt("nostats")["failure"])

    def test_an_output_mismatch_is_refused(self):
        report = self.attempt("mismatch", side="base")
        self.assertIn("differs from the reference", report["failure"])
        self.assertNotIn("blocked", report)

    def test_a_stray_product_write_is_refused(self):
        report = self.attempt("stray")
        self.assertIn("stray write: stray.txt", report["failure"])

    def test_a_selftest_that_writes_into_its_directory_is_refused(self):
        report = self.attempt("stray", name="reduce-selftest")
        self.assertIn("stray write", report["failure"])

    def test_an_extension_module_is_refused(self):
        report = self.attempt("extension", side="base")
        self.assertIn("extension module(s) loaded: simpExt",
                      report["failure"])
        self.assertNotIn("blocked", report)

    def test_a_loaded_path_outside_the_root_is_refused(self):
        self.assertIn("outside the root",
                      self.attempt("outside")["failure"])
        self.assertIn("runs in /elsewhere", self.attempt(
            "holdir", at=1000)["failure"] if False else
            self.attempt("holdir", name="reduce-selftest")["failure"])

    def test_a_candidate_finding_blocks_and_is_judged(self):
        report = self.attempt("extension", side="cand")
        self.assertIn("blocked", report)
        self.assertEqual(self.world.status()[-1][1], ["blocked"])
        with self.assertRaisesRegex(dw.Refusal, "judged attempt"):
            self.world.run("again", self.world.spec(["logroot"]))

    def test_a_candidate_output_mismatch_is_a_finding_too(self):
        report = self.attempt("mismatch", side="cand")
        self.assertIn("blocked", report)

    def test_a_failure_before_any_measurement_is_void_and_may_be_redone(self):
        self.attempt("exit", at=1)
        found = dw.read_ledger(dw.ledger_path(self.world.repo))[1]
        (key,) = found
        self.assertIsNone(dw.judged_because(key[0], key[1], found[key]))
        self.world.fault = None
        report = self.world.run("redo", self.world.spec(["logroot"]))
        self.assertTrue(report["success"], report.get("failure"))

    def test_a_failure_after_admitted_processes_is_a_judged_draw(self):
        report = self.attempt("exit", at=6)
        self.assertGreater(len(report["runs"]), 1)
        found = dw.read_ledger(dw.ledger_path(self.world.repo))[1]
        (key,) = found
        self.assertIn("admitted", dw.judged_because(key[0], key[1],
                                                    found[key]))
        self.world.fault = None
        with self.assertRaisesRegex(dw.Refusal, "judged attempt already"):
            self.world.run("redo", self.world.spec(["logroot"]))
        self.assertFalse(Path(self.world.tmp / "redo").exists())

    def test_a_failing_snapshot_verification_is_a_void_refusal(self):
        report = self.world.run(
            "v", self.world.spec(["logroot"]),
            verify_argv=[sys.executable, "-c", "import sys; sys.exit(1)"])
        self.assertFalse(report["success"])
        self.assertIn("verification failed", report["failure"])
        self.assertEqual(report["runs"], [])
        self.assertFalse(self.world.calls)

    def test_a_decision_stage_cannot_skip_the_verification(self):
        with self.assertRaisesRegex(dw.Refusal, "needs the snapshot"):
            self.world.run("n", self.world.spec(["logroot"]),
                           no_verify=True)

    def test_unauthorized_runs_do_not_start(self):
        with self.assertRaises(dw.Refusal):
            self.world.run("u", self.world.spec(["logroot"]),
                           authorize_measurements=False)
        self.assertFalse(self.world.calls)

    def test_the_manifest_must_name_the_given_roots(self):
        with self.assertRaises(dw.Refusal):
            self.world.run("m", self.world.spec(["logroot"]),
                           cand_root=self.world.tmp / "base")


class Processes(Base):
    def test_theory_processes_restore_the_products_byte_for_byte(self):
        before = self.world.snapshot()
        report = self.world.run("ok", self.world.spec(["logroot"]))
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(self.world.snapshot(), before)
        self.assertEqual(len(report["runs"]), 40)
        self.assertEqual(report["outcome"]["digests"].keys(), {"logroot"})

    def test_commands_and_environment_of_the_units(self):
        self.world.run("c", self.world.spec(["logroot", "reduce-selftest"],
                                            pairs=10))
        theory = next(c for c in self.world.calls if c[0] == "logroot")
        env = theory[2]
        self.assertEqual(env["PATH"], dw.SANE_PATH)
        self.assertEqual((env["LC_ALL"], env["TZ"], env["TERM"]),
                         ("C", "UTC", "dumb"))
        self.assertTrue(env["POLY_CLINE_OPTIONS"].endswith("T32Report.uo"))
        self.assertNotIn("HOLSELFTESTLEVEL", env)
        self.assertTrue(env["HOME"].endswith("/home"))
        test = next(c for c in self.world.calls
                    if c[0] == "reduce-selftest")
        self.assertEqual(test[2]["HOLSELFTESTLEVEL"], dw.SELFTEST_LEVEL)
        self.assertNotIn("POLY_CLINE_OPTIONS", test[2])
        sides = {c[1] for c in self.world.calls}
        self.assertEqual(sides, {"base", "cand"})

    def test_the_selftest_command_puts_the_reporter_before_the_last_argument(
            self):
        root = self.world.roots["base"]
        unit = cases.BY_NAME["boss-selftest"]
        argv, cwd = dw.unit_argv(unit, root, "/rep/T32Report.uo")
        self.assertEqual(argv[-2:], ["/rep/T32Report.uo", "selftest"])
        self.assertEqual(argv[:3], [str(root / "bin/hol"),
                                    "--gcthreads=1", "run"])
        self.assertEqual(cwd, root / "src/boss")

    def test_scratch_is_removed_and_ledger_lines_are_chained(self):
        self.world.run("ok", self.world.spec(["logroot"]))
        self.assertFalse(list(self.world.tmp.glob("scratch/*")))
        state = dw.tg.Ledger(dw.ledger_path(self.world.repo))
        self.assertEqual([r["event"] for r in state.records],
                         ["open", "close"])

    def test_the_negative_control_detects_the_busy_reporter(self):
        spec = dw.info_spec(self.world.args("n", reps=1), "control")
        report = dw.run_stage(self.world.args("n", reps=1), spec)
        self.assertTrue(report["success"], report.get("failure"))
        control = report["outcome"]["negative_control"]
        self.assertTrue(control["detected"], control)
        self.assertEqual(control["unit"], "logroot")
        busy = [c for c in self.world.calls if "T32_BUSY" in c[2]]
        self.assertEqual(len(busy), 10)
        self.assertEqual({c[1] for c in self.world.calls}, {"base"})
        info = dw.tg.Ledger(dw.ledger_path(self.world.repo)).records
        self.assertEqual([r["event"] for r in info], ["info", "info-end"])
        self.assertEqual(dw.exit_of(report), 0)

    def test_the_negative_control_is_missed_without_the_busy_loop(self):
        self.world.launch_plain = self.world.launch

        def plain(argv, cwd, env, timeout, out, fds=()):
            env = {k: v for k, v in env.items() if k != "T32_BUSY"}
            return self.world.launch_plain(argv, cwd, env, timeout, out, fds)
        with mock.patch.object(dw, "launch", plain):
            report = dw.run_stage(self.world.args("n"), dw.info_spec(
                self.world.args("n", reps=1), "control"))
        self.assertFalse(report["outcome"]["negative_control"]["detected"])
        self.assertEqual(dw.exit_of(report), 1)

    def test_smoke_runs_both_sides_and_compares_outputs(self):
        args = self.world.args("s", only=["logroot", "boss-selftest"])
        report = dw.run_stage(args, dw.info_spec(args, "smoke"))
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(len(report["runs"]), 4)
        self.assertEqual(sorted(report["outcome"]["digests"]),
                         ["boss-selftest", "logroot"])
        self.world.fault = lambda u, s, n: (
            "mismatch" if s == "cand" and u["kind"] == "selftest" else None)
        args = self.world.args("s2", only=["boss-selftest"])
        report = dw.run_stage(args, dw.info_spec(args, "smoke"))
        self.assertFalse(report["success"])

    def test_decision_stages_refuse_a_subset_of_the_workloads(self):
        args = self.world.args("o", only=["logroot"])
        self.assertEqual(dw.info_spec(args, "smoke")["names"], ["logroot"])
        self.assertEqual(dw.info_spec(args, "control")["names"],
                         [cases.CONTROL_UNIT])


class Replay(Base):
    def stage(self, scale=1.05, noise=0.001, name="r"):
        self.world.profile["logroot"] = (scale, noise)
        report = self.world.run(name, self.world.spec(["logroot"]))
        self.assertTrue(report["success"], report.get("failure"))
        return report

    def test_replay_recomputes_the_decision_byte_for_byte(self):
        report = self.stage()
        self.assertEqual(report["outcome"]["results"]["logroot"]["decision"],
                         "fail")
        info, again = dw.replay_one(self.world.tmp / "r",
                                    ledger=dw.ledger_path(self.world.repo))
        self.assertEqual(info["exit"], "fail")
        self.assertEqual(info["attempts"], dict(attempts=1, judged=1))
        self.assertEqual(dw.dumps(again), dw.dumps(report))
        receipts = [a.load(self.world.tmp / "r" / r["receipt"])
                    for r in report["runs"]]
        self.assertEqual(dw.dumps(dw.outcome(report, receipts)),
                         dw.dumps(report["outcome"]))

    def test_replay_refuses_a_changed_receipt_or_report(self):
        self.stage()
        folder = self.world.tmp / "r"
        ledger = dw.ledger_path(self.world.repo)
        path = folder / "logroot-candidate-000-baseline-00.json.gz"
        original = path.read_bytes()
        receipt = json.loads(gzip.decompress(original))
        receipt["usage"]["utime"] *= 0.5
        path.write_bytes(gzip.compress(json.dumps(receipt).encode()))
        with self.assertRaisesRegex(dw.Refusal, "changed process receipt"):
            dw.replay_one(folder, ledger=ledger)
        path.write_bytes(original)
        dw.replay_one(folder, ledger=ledger)
        report = a.load(folder / "downstream.json")
        report["outcome"]["results"]["logroot"]["decision"] = "pass"
        (folder / "downstream.json").write_text(json.dumps(report))
        with self.assertRaises(dw.Refusal):
            dw.replay_one(folder, ledger=ledger)

    def test_replay_refuses_a_forged_measurement_in_a_resealed_receipt(self):
        report = self.stage()
        folder = self.world.tmp / "r"
        entry = report["runs"][5]
        path = folder / entry["receipt"]
        receipt = json.loads(gzip.decompress(path.read_bytes()))
        receipt["measurement"]["raw"]["cpu"] *= 0.5
        data = gzip.compress((dw.dumps(receipt)).encode(), mtime=0)
        path.write_bytes(data)
        report["runs"][5]["seal"] = a.seal(path)
        (folder / "downstream.json").write_text(dw.dumps(report))
        with self.assertRaisesRegex(dw.Refusal, "changed measurement"):
            dw.replay_one(folder, ledger=dw.ledger_path(self.world.repo))

    def test_replay_checks_the_ledger_close_and_the_draw_count(self):
        self.stage()
        folder = self.world.tmp / "r"
        ledger = dw.ledger_path(self.world.repo)
        with self.assertRaises(dw.Refusal):
            dw.replay_one(folder, ledger=self.world.tmp / "none.jsonl")
        report = a.load(folder / "downstream.json")
        report["key"] = "0" * 64
        (folder / "downstream.json").write_text(dw.dumps(report))
        with self.assertRaises(dw.Refusal):
            dw.replay_one(folder, ledger=ledger)

    def test_replay_runs_no_process(self):
        self.stage()
        calls = len(self.world.calls)
        dw.replay_one(self.world.tmp / "r",
                      ledger=dw.ledger_path(self.world.repo))
        self.assertEqual(len(self.world.calls), calls)

    def test_a_pass_replays_as_a_pass(self):
        self.stage(scale=1.0, name="p")
        info, _ = dw.replay_one(self.world.tmp / "p",
                                ledger=dw.ledger_path(self.world.repo))
        self.assertEqual(info["exit"], "pass")


class CountsCommit(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory(prefix="t32-counts-")
        self.addCleanup(self.dir.cleanup)
        self.repo = Path(self.dir.name)
        git(self.repo, "init", "-q")
        (self.repo / "src/simp/tests/performance").mkdir(parents=True)
        (self.repo / "src/simp/tests/performance/keep").write_text("x")
        (self.repo / "compiled.sml").write_text("1")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "cand")
        self.cand = git(self.repo, "rev-parse", "HEAD")
        self.path = self.repo / "src/simp/tests/performance/counts.json"

    def commit(self, *paths):
        git(self.repo, "add", *paths)
        git(self.repo, "commit", "-q", "-m", "c")
        return git(self.repo, "rev-parse", "HEAD")

    def test_counts_committed_alone_are_accepted(self):
        self.path.write_text("{}")
        head = self.commit("src")
        self.assertEqual(dw.check_counts_commit(self.repo, self.path,
                                                self.cand), head)

    def test_uncommitted_counts_are_refused(self):
        self.path.write_text("{}")
        with self.assertRaisesRegex(dw.Refusal, "not committed"):
            dw.check_counts_commit(self.repo, self.path, self.cand)

    def test_a_commit_that_carries_other_files_is_refused(self):
        self.path.write_text("{}")
        (self.repo / "src/simp/tests/performance/code.py").write_text("x")
        self.commit("src")
        with self.assertRaisesRegex(dw.Refusal, "commit the counts alone"):
            dw.check_counts_commit(self.repo, self.path, self.cand)

    def test_counts_changed_by_two_commits_are_refused(self):
        self.path.write_text("{}")
        self.commit("src")
        self.path.write_text('{"a": 1}')
        self.commit("src")
        with self.assertRaises(dw.Refusal):
            dw.check_counts_commit(self.repo, self.path, self.cand)

    def test_modified_counts_are_not_the_committed_ones(self):
        self.path.write_text("{}")
        self.commit("src")
        self.path.write_text('{"a": 1}')
        with self.assertRaisesRegex(dw.Refusal, "not committed"):
            dw.check_counts_commit(self.repo, self.path, self.cand)

    def test_a_compiled_source_change_after_the_candidate_is_refused(self):
        self.path.write_text("{}")
        self.commit("src")
        (self.repo / "compiled.sml").write_text("2")
        self.commit("compiled.sml")
        with self.assertRaisesRegex(dw.Refusal, "outside"):
            dw.check_counts_commit(self.repo, self.path, self.cand)


class Chain(Base):
    """smoke -> pilot -> counts -> first stage -> second stage -> follow-up
    -> disposition, on fake processes: logroot is noisy in the first stage
    (a control outside the window), borderline at 3% in the second, and
    passes in the follow-up; every other workload passes in the first."""

    @classmethod
    def commit_counts(cls, world, path):
        rel = os.path.relpath(path, world.repo)
        git(world.repo, "add", rel)
        git(world.repo, "commit", "-q", "-m", "counts " + path.name)

    def test_the_whole_chain(self):
        w = self.world
        ledger = dw.ledger_path(w.repo)
        perf = w.repo / "src/simp/tests/performance"
        all_args = w.args("smoke")
        smoke = dw.run_stage(all_args, dw.info_spec(all_args, "smoke"))
        self.assertTrue(smoke["success"], smoke.get("failure"))
        self.assertEqual(len(smoke["runs"]), 30)
        args = w.args("pilot")
        pilot = dw.run_stage(args, dw.info_spec(args, "pilot"))
        self.assertTrue(pilot["success"], pilot.get("failure"))
        self.assertEqual(len(pilot["runs"]), 150)
        self.assertTrue(pilot["outcome"]["covered"])
        self.assertEqual({p["reps"] for p in
                          pilot["outcome"]["pilot"].values()}, {1})
        self.assertEqual({c[1] for c in w.calls[30:]}, {"base"})
        # predeclare
        counts = dw.predeclare_first(w.args("x", pilot=w.tmp / "pilot",
                                            smoke=w.tmp / "smoke"))
        self.assertEqual(set(counts["reps"]), set(cases.NAMES))
        counts_path = perf / "counts.json"
        with self.patch_code():
            counts_path.write_text(dw.dumps(counts))
            with self.assertRaisesRegex(dw.Refusal, "not committed"):
                dw.first_spec(w.args("a", counts=counts_path))
            self.commit_counts(w, counts_path)
            # first stage
            for name in cases.NAMES:
                w.profile[name] = (1.0, 0.001)
            w.profile["logroot"] = (1.0, 0.06)
            spec = dw.first_spec(w.args("first", counts=counts_path))
            first = dw.run_stage(w.args("first", counts=counts_path), spec)
            self.assertTrue(first["success"], first.get("failure"))
            self.assertEqual(len(first["runs"]), 15 * 20 * 4)
            res = first["outcome"]["results"]
            self.assertEqual(
                [n for n in cases.NAMES if res[n]["decision"] != "pass"],
                ["logroot"])
            self.assertFalse(res["logroot"]["control_valid"])
            self.assertTrue(all(res[n]["control_valid"]
                                for n in cases.NAMES if n != "logroot"))
            self.assertEqual(dw.exit_of(first), 2)
            # a second first stage is refused, and so is replaying wrong
            with self.assertRaisesRegex(dw.Refusal, "judged attempt"):
                w.run("first-again", spec, counts=counts_path)
            chain = dw.replay_chain(w.tmp / "first", ledger,
                                    counts=counts_path, repo=w.repo)
            self.assertEqual([e["stage"] for e in chain], ["first"])
            owed = dw.disposition(chain, ledger)
            self.assertEqual(owed["status"], "blocked")
            self.assertEqual(owed["workloads"]["logroot"]["note"],
                             "second stage owed")
            # second stage: only logroot, the pairs the grid's rule gives
            w.profile["logroot"] = (1.03, 0.01)
            sargs = w.args("second", first=w.tmp / "first",
                           counts=counts_path)
            spec2 = dw.second_spec(sargs)
            self.assertEqual(spec2["names"], ["logroot"])
            self.assertEqual(spec2["pairs"]["logroot"],
                             res["logroot"]["second_stage_pairs"])
            second = dw.run_stage(sargs, spec2)
            self.assertTrue(second["success"], second.get("failure"))
            sres = second["outcome"]["results"]["logroot"]
            self.assertEqual(sres["decision"], "inconclusive")
            self.assertTrue(sres["control_valid"])
            chain = dw.replay_chain(w.tmp / "second", ledger,
                                    counts=counts_path, repo=w.repo)
            self.assertEqual([e["stage"] for e in chain],
                             ["first", "second"])
            disp = dw.disposition(chain, ledger)
            self.assertEqual(disp["workloads"]["logroot"]["status"],
                             "followup")
            self.assertEqual(disp["status"], "blocked")
            self.assertEqual(disp["counts"]["followup"], 1)
            with self.assertRaises(dw.Refusal):  # at most one second stage
                w.run("second-again", spec2)
            # follow-up: the same driver, its own counts, committed alone
            fargs = w.args("fu", stage=w.tmp / "second", followup=True,
                           counts=counts_path)
            fcounts = dw.predeclare_followup(fargs)
            self.assertEqual(fcounts["workloads"], ["logroot"])
            self.assertEqual(fcounts["pairs"]["logroot"],
                             2 * sres["pairs"])
            self.assertNotEqual(fcounts["seed"], dw.EXTENSION_SEED)
            fpath = perf / "followup.json"
            fpath.write_text(dw.dumps(fcounts))
            fa = w.args("followup", followup_counts=fpath,
                        counts=counts_path)
            with self.assertRaisesRegex(dw.Refusal, "not committed"):
                dw.followup_spec(fa)
            self.commit_counts(w, fpath)
            w.profile["logroot"] = (1.0, 0.01)
            fspec = dw.followup_spec(fa)
            follow = dw.run_stage(fa, fspec)
            self.assertTrue(follow["success"], follow.get("failure"))
            self.assertEqual(follow["outcome"]["results"]["logroot"][
                "decision"], "pass")
            self.assertEqual(dw.exit_of(follow), 0)
            chain = dw.replay_chain(w.tmp / "followup", ledger,
                                    counts=counts_path,
                                    followup_counts=fpath, repo=w.repo)
            self.assertEqual([e["stage"] for e in chain],
                             ["first", "second", "followup"])
            self.assertEqual(dw.dumps(chain[-1]["report"]),
                             dw.dumps(follow))
            disp = dw.disposition(chain, ledger)
            self.assertEqual(disp["status"], "pass")
            self.assertEqual(disp["counts"]["pass"], 15)
            self.assertEqual(len(disp["attempts"]), 3)
            self.assertFalse(any(r["void"] for r in disp["attempts"]))
            # the follow-up cannot be repeated
            with self.assertRaises(dw.Refusal):
                w.run("followup-again", fspec, counts=counts_path)
            # the drivers' main entry points reach the same results
            out = w.tmp / "disposition.json"
            code = dw.main(["dispose", "--stage", str(w.tmp / "followup"),
                            "--out", str(out), "--ledger", str(ledger),
                            "--counts", str(counts_path),
                            "--followup-counts", str(fpath),
                            "--repo", str(w.repo)])
            self.assertEqual(code, 0)
            self.assertEqual(json.loads(out.read_text())["status"], "pass")
            code = dw.main(["replay", str(w.tmp / "followup"), "--ledger",
                            str(ledger), "--counts", str(counts_path),
                            "--followup-counts", str(fpath), "--repo",
                            str(w.repo)])
            self.assertEqual(code, 0)
        # the code the counts are bound to cannot change under them
        with mock.patch.object(dw, "code_seals",
                               lambda: dict(counts["code"], x="y")):
            with self.assertRaisesRegex(dw.Refusal, "code changed"):
                dw.load_counts(counts_path, *dw.pins_of(w.args("z")),
                               "first", w.repo)

    def patch_code(self):
        """The counts commits sit in the temporary repository, while the
        sealed code is that of this checkout: nothing to patch there; the
        repository check of the candidate is already replaced."""
        return mock.patch.object(dw, "COUNTS_SCOPE",
                                 "src/simp/tests/performance/")


if __name__ == "__main__":
    unittest.main()
