#!/usr/bin/env python3
"""TASK32 proof-build timing driver (task32_downstream.py), on fake trees and
fake processes: synthetic rows, refusals, restore and its journal, signals,
schedule, counts commit rules, replay, the verify interface of
task32_snapshots, and a whole smoke -> pilot -> control -> counts -> first
stage -> second stage -> follow-up -> disposition chain."""
import argparse
import contextlib
import gzip
import io
import json
import os
from pathlib import Path
import random
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock

import acceptance as a
import loading
import task32_cases as cases
import task32_downstream as dw
import task32_snapshots as snap
from test_task32_snapshots import mk_dat

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


NUM_DEPS = ["Arith", "Norm", "Solve", "numLib", "Defn"]
REAL_DEPS = ["realLib", "metricTheory"]
HEAP_MAKEFILES = {
    "src/num/termination": "ARITH_DEPS = Arith Norm \\\n  Solve\n"
    "BARE_DEPS = ../numLib ../../tfl/src/Defn \\\n"
    "  $(patsubst %,../arith/src/%,$(ARITH_DEPS))\nDEPS = $(BARE_DEPS)\n",
    "src/real/analysis": "REAL_DEPS = realLib metricTheory\n"
    "BARE_DEPS = $(patsubst %,../%,$(REAL_DEPS))\n"}


def preloaded(heap):
    """What a process of the heap finds loaded: each heap holds the one it
    was built on and its own Holmakefile's modules."""
    base = ["Lib", "Thm"]
    if heap == cases.NUMHEAP:
        return base + NUM_DEPS
    if heap == "bin/hol.state0":
        return base
    state = base + ["boss"]
    return state if heap == "bin/hol.state" else state + REAL_DEPS


STAT_FIELDS = dict(gc_full=1, gc_partial=3, gc_share=0, size_heap=1 << 20)
BUILD_LOG = "selftest ok (0.0s)\n"


class World:
    """Two fake snapshots with the 15 units' directories and prebuilt
    products, a git repository for the ledger, the journals and the counts
    commits, and a fake `launch` that plays the processes."""

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
            self.build_tree(root)
        self.manifest = self.tmp / "snapshots.json"
        self.write_manifest()
        self.profile = {}  # workload -> (candidate scale, noise)
        self.default = (1.0, 0.001)
        self.counter = 0
        self.fault = None  # (unit, side, n) -> kind or None
        self.calls = []
        self.ignore_busy = False

    def write_manifest(self, **change):
        sides = {}
        for (label, root), pin in zip(self.roots.items(),
                                      (self.base_pin, self.cand_pin)):
            sides[label] = dict(root=str(root), pin=pin, tree=pin,
                                label=label, incomplete=False)
            sides[label].update(change.get(label, {}))
        self.manifest.write_text(json.dumps(dict(
            schema=change.get("schema", snap.SCHEMA), sides=sides)))

    def build_tree(self, root):
        (root / "bin").mkdir(parents=True)
        for n in ("Holmake", "hol", "hol.state0"):
            (root / "bin" / n).write_text("x")
        for rel, text in HEAP_MAKEFILES.items():
            (root / rel).mkdir(parents=True, exist_ok=True)
            (root / rel / "Holmakefile").write_text(text)
        (root / "sigobj").mkdir()
        (root / "sigobj/Lib.ui").symlink_to(root / "bin/hol")
        for unit in cases.UNITS:
            folder = root / unit["dir"]
            for sub in (".hol/objs", ".hol/docs", ".hol/logs",
                        ".hol/make-deps", ".hol/locks", "sub/.hol"):
                (folder / sub).mkdir(parents=True, exist_ok=True)
            if unit["kind"] == "theory":
                self.write_products(folder, unit["theory"], root, "sig")
            else:
                (folder / "selftest.exe").write_text(
                    "#!/bin/sh\nset -e\n%s/bin/hol --gcthreads=1 run "
                    "--holstate=%s  selftest\nexit 0\n" % (
                        root, root / unit["heap"]))
                (folder / (".hol/logs/%s.log" % unit["name"])).write_text(
                    BUILD_LOG)
            (folder / "other.sml").write_text("val x = 1\n")
            os.utime(folder / "other.sml", ns=(10 ** 18, 10 ** 18))
            (folder / ".hol/make-deps/other.d").write_text("deps\n")

    @staticmethod
    def write_products(folder, name, root, sig):
        """The products a theory target writes: real-format .dat, root in the
        .sig and .sml, the make-deps files the run rewrites."""
        text = dict(sig="%s %s %s\n" % (sig, name, root),
                    dat=mk_dat(name), sml="sml %s %s\n" % (name, root))
        for ext in ("sig", "dat", "uo", "ui", "sml", "cachekey"):
            path = folder / ".hol/objs" / ("%sTheory.%s" % (name, ext))
            path.write_text(text.get(ext, "%s %s\n" % (ext, name)))
            os.utime(path, ns=(2 * 10 ** 18, 2 * 10 ** 18))
        (folder / ".hol/docs" / ("%sTheory.html" % name)).write_text("h\n")
        for rel in (".hol/make-deps/%sTheory.sig.d" % name,
                    ".hol/make-deps/%sScript.sml.d" % name):
            (folder / rel).write_text("deps %s\n" % name)
            os.utime(folder / rel, ns=(3 * 10 ** 18, 3 * 10 ** 18))

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
        cpu = unit["serial"] * factor
        if "T32_BUSY" in env and not self.ignore_busy:
            cpu += float(env["T32_BUSY"])  # absolute seconds
        fault = self.fault and self.fault(unit, side, self.counter)
        uo = env.get("POLY_CLINE_OPTIONS") or argv[-2]
        stats = dict(schema=dw.STATS_SCHEMA, nongc_usr=cpu * 0.9,
                     nongc_sys=cpu * 0.05, gc_usr=cpu * 0.04,
                     gc_sys=cpu * 0.01, gc_time=cpu * 0.05 * (
                         1 + 0.2 * rng.random()), holdir=str(root),
                     loaded_before=preloaded(unit["heap"]),
                     loaded=["Foo"],
                     files=[["Foo.sml", str(root / "src/foo")],
                            ["T32Report.sml", str(Path(uo).parent)]],
                     **STAT_FIELDS)
        if fault == "noreporter":
            stats["files"] = stats["files"][:1]
        if fault == "newstem":
            stats["loaded"] = ["Foo", "Zed"]
        code = 0
        if theory:
            sig = "bad" if fault == "mismatch" else "sig"
            self.write_products(cwd, unit["theory"], root, sig)
            for rel in (".hol/make-deps/%sTheory.sig.d" % unit["theory"],
                        ".hol/make-deps/%sScript.sml.d" % unit["theory"]):
                os.utime(cwd / rel, ns=(4 * 10 ** 18, 4 * 10 ** 18))
            if fault == "stray":
                (cwd / "stray.txt").write_text("x")
            if fault in ("exit", "leftover"):
                (cwd / (".hol/objs/%sScript.uo" % unit["theory"])
                 ).write_text("junk")
                (cwd / (unit["theory"] + "Script")).write_text("junk")
                (cwd / ".hol/objs/part.dumpedheap").write_text("junk")
            if fault == "churn":
                (cwd / ".hol/make-deps/other.d").write_text("changed\n")
            if fault == "cache":
                (cwd / ".hol/make-deps/FooTheory.sig.d").write_text("d\n")
                (cwd / "sub/.hol/make-deps").mkdir()
                (cwd / "sub/.hol/make-deps/B.sml.d").write_text("d\n")
            deps = cwd.parents[2] / "src/integer/.hol/make-deps"
            if fault == "xcache":
                (deps / "IncTheory.sig.d").write_text("d\n")
            if fault == "xnewdir":
                made = cwd.parents[2] / "src/boss/.hol/make-deps"
                made.mkdir()
                (made / "BTheory.sml.d").write_text("d\n")
            if fault == "newhol":
                (cwd / "fresh/.hol/make-deps").mkdir(parents=True)
                (cwd / "fresh/.hol/make-deps/C.d").write_text("d\n")
            if fault == "xsubdir":
                (deps / "sub").mkdir()
                (deps / "sub/x.d").write_text("d\n")
            if fault == "xbare":
                (cwd.parent / ".hol/make-deps").mkdir(parents=True)
                (cwd.parent / ".hol/make-deps/x.d").write_text("d\n")
            if fault == "xother":
                (deps / "inc.txt").write_text("x")
            if fault == "xmodify":
                (deps / "other.d").write_text("changed\n")
            if fault == "other":
                (cwd / ".hol/other.txt").write_text("x")
            if fault == "outsided":
                (cwd / "foo.d").write_text("x")
            if fault == "modify":
                (cwd / "other.sml").write_text("val x = 2\n")
            out = "Holmake: built %s in %.2fs\n" % (unit["name"],
                                                    rng.random())
        else:
            tag = "[GC = 0.015] " if rng.random() < 0.5 else ""
            out = "%sselftest ok (%.1fs)\n" % (tag, rng.uniform(1, 5))
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
        if fault == "terminate":
            raise snap.Terminated("SIGTERM")
        if fault == "exit":
            code = 1
        Path(out_path).write_text(out)
        if fault != "nostats":
            Path(env["T32_STATS"]).write_text(json.dumps(stats) + "\n")
        return dict(exit=code, timed_out=False, wall=cpu * 1.03,
                    utime=cpu * 0.9, stime=cpu * 0.1, maxrss=10 ** 8,
                    survivors=[])

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
            counts=None, output=self.tmp / name,
            scratch=self.tmp / "scratch", timeout=60,
            verify_argv=[sys.executable, "-c", "pass"], no_verify=False,
            authorize_measurements=True, only=[], reps=1,
            followup_counts=None, pilot=None, smoke=None, control=None,
            ledger=None)
        values.update(extra)
        return argparse.Namespace(**values)

    def spec(self, names, pairs=10, stage="first", seed=None, reps=1,
             busy=None):
        return dict(mode=stage, stage=stage, names=names,
                    pairs={w: pairs for w in names},
                    reps={w: reps for w in names},
                    seed=seed or dw.SEEDS[stage], references=None,
                    busy=busy)

    def info(self, name, mode, names=None, **extra):
        args = self.args(name, only=names or [], **extra)
        return args, dw.info_spec(args, mode)

    def run(self, name, spec, **extra):
        return dw.run_stage(self.args(name, **extra), spec)

    def ledger(self):
        return dw.ledger_path(self.repo)

    def status(self):
        found = dw.read_ledger(self.ledger())[1]
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
        self.assertLessEqual(res["second_stage_pairs"], 120)

    def test_followup_pairs_are_the_first_stages_second_stage_rule(self):
        first = {"a": dict(second_stage_pairs=40),
                 "b": dict(second_stage_pairs=70)}
        self.assertEqual(dw.followup_pairs(first, ["b"]), {"b": 70})

    def test_statistics_refuse_a_reordered_or_rejected_schedule(self):
        good = rows(lambda i: 5.0, lambda i: 5.0)
        with self.assertRaises(dw.Refusal):
            dw.statistics(list(reversed(good)), 20, 1)
        bad = [dict(r) for r in good]
        bad[3]["accepted"] = False
        with self.assertRaises(dw.Refusal):
            dw.statistics(bad, 20, 1)

    def test_classification_follows_the_task31_routing(self):
        def res(decision, valid):
            return dict(decision=decision, control_valid=valid)
        c = dw.classify
        self.assertEqual(c([("first", res("pass", True))])[0], "pass")
        self.assertEqual(c([("first", res("fail", False))])[0], "fail")
        # control-limited: the second stage
        self.assertEqual(c([("first", res("inconclusive", False))]),
                         ("blocked", dw.NOTE_SECOND))
        # inconclusive with a valid control: the follow-up, after the
        # first stage already
        self.assertEqual(c([("first", res("inconclusive", True))])[0],
                         "followup")
        chain = [("first", res("inconclusive", False)),
                 ("second", res("inconclusive", True))]
        self.assertEqual(c(chain)[0], "followup")
        self.assertEqual(c(chain[:1] + [("second", res(
            "inconclusive", False))])[0], "blocked")
        for last in ("inconclusive", "fail", "pass"):
            got = c(chain + [("followup", res(last, True))])[0]
            self.assertEqual(got, last if last != "inconclusive"
                             else "blocked")
        self.assertEqual(c(chain[:1] + [("second", res("pass", True))])[0],
                         "pass")


class Schedule(unittest.TestCase):
    def test_round_robin_with_ab_ba_pairs_and_alternating_phases(self):
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
        # control first on even rounds, candidate first on odd rounds
        for i, before, after in ((0, "control", "candidate"),
                                 (1, "candidate", "control"),
                                 (2, "control", "candidate")):
            phases = [o[1] for o in order if o[0] == "x" and o[2] == i]
            self.assertEqual(phases, [before] * 4 + [after] * 4)

    def test_control_processes_run_in_the_base_snapshot(self):
        self.assertEqual(dw.side_of("control", "candidate"), "base")
        self.assertEqual(dw.side_of("candidate", "baseline"), "base")
        self.assertEqual(dw.side_of("candidate", "candidate"), "cand")
        self.assertEqual(dw.side_of("pilot", "candidate"), "base")
        self.assertEqual(dw.side_of("smoke", "candidate"), "cand")
        self.assertEqual(dw.side_of("candidate", "candidate", True), "base")

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
        self.assertIn("cpu () + seconds", text)  # absolute busy seconds
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

    def test_selftest_normalization_is_the_snapshots_rule_set(self):
        root = "/r"
        text = ("\x1b[1mok\x1b[0m /r/x took 12.5s [GC = 0.015] done "
                "(0.003s) runtime: 3.2s\n").encode()
        self.assertEqual(dw.normalize_text(text, root),
                         snap.normalize_log(text, root))
        # a GC tag in one process and none in another: the same digest
        one = b"Testing x ...  [GC = 0.015] (0.003s) OK\n"
        two = b"Testing x ...  (0.9s) OK\n"
        self.assertEqual(dw.text_digest(one, root),
                         dw.text_digest(two, root))
        self.assertNotEqual(dw.text_digest(one, root),
                            dw.text_digest(b"Testing y ...\n", root))
        self.assertEqual(
            dw.normalize_text(text, root),
            "ok $(HOLDIR)/x took 12.5s done (<TIME>) runtime: <TIME>\n")

    def test_theory_digest_uses_the_canonical_dat_sig_and_sml(self):
        root = Path("/r1")
        files = dict(sig=b"s /r1", sml=b"m /r1", dat=mk_dat("x").encode())
        base = dw.theory_digest(files, root)
        # the same theory with its tables in another order, in another root
        other = mk_dat("x", strings=["x", "c", "bool", "min"],
                       types=["bool", "alpha"], terms=["c", "x", "ap"])
        files2 = dict(sig=b"s /r2", sml=b"m /r2", dat=other.encode())
        self.assertEqual(dw.theory_digest(files2, Path("/r2")), base)
        # a changed theorem, .sig or generated .sml is another digest
        for change in (dict(dat=mk_dat("x", tags=("OTHER",)).encode()),
                       dict(sig=b"s2 /r1"), dict(sml=b"m2 /r1")):
            self.assertNotEqual(dw.theory_digest(dict(files, **change), root),
                                base, change)
        for ext in ("sig", "dat", "sml"):
            with self.assertRaises(dw.Refusal):
                dw.theory_digest({k: v for k, v in files.items()
                                  if k != ext}, root)
        with self.assertRaisesRegex(dw.Refusal, "unparsable"):
            dw.theory_digest(dict(files, dat=b"z"), root)

    def test_the_build_log_digest_of_a_selftest(self):
        with tempfile.TemporaryDirectory() as tmp:
            folder = Path(tmp)
            unit = cases.BY_NAME["arith-selftest"]
            with self.assertRaisesRegex(dw.Refusal, "no build log"):
                dw.build_log_digest(folder, unit, "/r")
            (folder / ".hol/logs").mkdir(parents=True)
            (folder / ".hol/logs/x-selftest.log").write_bytes(
                b"ok [GC = 0.1] (1.5s)\n")
            first = dw.build_log_digest(folder, unit, "/r")  # the only log
            (folder / ".hol/logs/arith-selftest.log").write_bytes(
                b"ok (0.0s)\n")
            self.assertEqual(dw.build_log_digest(folder, unit, "/r"), first)

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

    def test_scans_use_the_snapshots_exclusions_and_stop_at_units(self):
        with tempfile.TemporaryDirectory() as tmp:
            folder = Path(tmp)
            for rel in (".hol/locks/a", ".hol/build-logs/b", ".hol/logs/c",
                        ".hol/logs/d-selftest.log", ".hol/objs/e",
                        "analysis/f", "g"):
                (folder / rel).parent.mkdir(parents=True, exist_ok=True)
                (folder / rel).write_text("x")
            got = {p for p, e in dw.scan(folder, ("analysis",)).items()
                   if e[0] == "f"}
            self.assertEqual(got, {".hol/logs/d-selftest.log",
                                   ".hol/objs/e", "g"})
            for rel in (".hol/locks/a", ".hol/build-logs/b", ".hol/logs/c"):
                self.assertTrue(snap.excluded(rel))
            self.assertEqual(
                dw.stops_for(cases.BY_NAME["real"]), ("analysis",))
            self.assertEqual(
                dw.stops_for(cases.BY_NAME["integer"]), ("testing",))
            self.assertEqual(dw.stops_for(cases.BY_NAME["lim"]), ())

    def test_settle_restores_products_moves_new_files_and_names_changes(self):
        with tempfile.TemporaryDirectory() as tmp:
            folder, store = Path(tmp, "d"), Path(tmp, "s")
            stray = Path(tmp, "stray")
            (folder / ".hol/objs").mkdir(parents=True)
            (folder / ".hol/make-deps").mkdir()
            path = folder / ".hol/objs/xTheory.dat"
            path.write_bytes(b"abc")
            os.utime(path, ns=(5 * 10 ** 18, 5 * 10 ** 18))
            dep = folder / ".hol/make-deps/xTheory.sig.d"
            dep.write_text("d")
            (folder / "keep.sml").write_text("k")
            before = dw.scan(folder)
            rels = snap.theory_target_files(folder, "x")
            self.assertEqual(sorted(rels),
                             [".hol/make-deps/xTheory.sig.d",
                              ".hol/objs/xTheory.dat"])
            meta = dw.back_up(folder, rels, store)
            for rel in rels:
                (folder / rel).unlink()
            # the process: rewrites its products, leaves intermediates,
            # makes a docs product that did not exist, edits keep.sml
            path.write_bytes(b"new")
            dep.write_text("changed")
            (folder / ".hol/objs/xScript.uo").write_text("junk")
            (folder / ".hol/docs").mkdir()
            (folder / ".hol/docs/xTheory.html").write_text("h")
            (folder / "keep.sml").write_text("edited")
            got = dw.settle(folder, (), before, meta, store, "x", stray)
            self.assertTrue(got["ok"])
            self.assertEqual(got["moved"], [".hol/objs/xScript.uo"])
            self.assertEqual(got["modified"], ["keep.sml"])
            self.assertEqual(got["rewritten"],
                             [".hol/docs/xTheory.html",
                              ".hol/make-deps/xTheory.sig.d",
                              ".hol/objs/xTheory.dat"])
            self.assertEqual((stray / ".hol/objs/xScript.uo").read_text(),
                             "junk")
            self.assertFalse((folder / ".hol/docs").exists())
            self.assertEqual(path.read_bytes(), b"abc")
            self.assertEqual(path.stat().st_mtime_ns, 5 * 10 ** 18)

    def test_move_stray_merges_directories_and_keeps_collisions(self):
        with tempfile.TemporaryDirectory(dir="/dev/shm") as tmp:
            tmp = Path(tmp)
            (tmp / "a/d").mkdir(parents=True)
            (tmp / "a/d/x").write_text("new")
            (tmp / "a/f").write_text("newf")
            (tmp / "s/a/d").mkdir(parents=True)
            (tmp / "s/a/d/y").write_text("old")
            (tmp / "s/a/f").write_text("oldf")
            dw.move_stray(tmp / "a", tmp / "s/a")
            self.assertFalse((tmp / "a").exists())
            self.assertEqual((tmp / "s/a/d/x").read_text(), "new")
            self.assertEqual((tmp / "s/a/d/y").read_text(), "old")
            self.assertEqual((tmp / "s/a/f").read_text(), "oldf")
            self.assertEqual((tmp / "s/a/f.1").read_text(), "newf")
            self.assertFalse((tmp / "s/a/d/d").exists())

    def test_an_outside_make_deps_that_cannot_be_removed_is_moved(self):
        with tempfile.TemporaryDirectory(dir="/dev/shm") as tmp:
            root = Path(tmp, "root")
            (root / "x/.hol").mkdir(parents=True)
            folder, stray = root / "u", Path(tmp, "stray")
            folder.mkdir()
            before = dw.list_make_deps(root, ["x"])
            (root / "x/.hol/make-deps").mkdir()
            with mock.patch.object(Path, "rmdir", side_effect=OSError):
                got = dw.settle_outside(root, folder, ["x"], before, [],
                                        stray)
            self.assertEqual(got["moved"], ["../x/.hol/make-deps"])
            self.assertTrue((stray / "x/.hol/make-deps").is_dir())
            self.assertFalse((root / "x/.hol/make-deps").exists())

    def test_a_directory_that_cannot_be_removed_is_moved_as_stray(self):
        with tempfile.TemporaryDirectory(dir="/dev/shm") as tmp:
            folder, stray = Path(tmp, "f"), Path(tmp, "stray")
            folder.mkdir()
            before = dw.scan(folder)
            (folder / "newdir").mkdir()
            with mock.patch.object(Path, "rmdir", side_effect=OSError):
                got = dw.settle(folder, (), before, {}, Path(tmp, "s"),
                                None, stray)
            self.assertEqual(got["moved"], ["newdir"])
            self.assertTrue((stray / "newdir").is_dir())
            self.assertFalse((folder / "newdir").exists())

    def test_validate_names_each_refusal(self):
        usage = dict(exit=0, timed_out=False, wall=1.0, utime=1.0,
                     stime=0.0, maxrss=1)
        rec = dict(usage=usage, stats=self.good, stray=[], modified=[],
                   churn=[], digest="d")
        unit = cases.BY_NAME["logroot"]
        dw.validate(rec, unit, Path("/r"), "/rep", "d", False)
        for change, text in (
                (dict(usage=dict(usage, exit=1)), "failed"),
                (dict(usage=dict(usage, timed_out=True)), "timed out"),
                (dict(stats=None), "missing stats"),
                (dict(stray=["a.txt"]), "stray write"),
                (dict(stray=["a.sml"], modified=["a.sml"]),
                 "snapshot must be rebuilt"),
                (dict(churn=["x.d"]), "churn that is not Holmake's"),
                (dict(churn=[".hol/make-deps/sub/x.d"]), "churn that is"),
                (dict(churn=["../../../../x/.hol/make-deps/a.d"]),
                 "churn that is"),
                (dict(digest="e"), "differs")):
            with self.assertRaisesRegex(dw.Refusal, text):
                dw.validate(dict(rec, **change), unit, Path("/r"), "/rep",
                            "d", False)
        with self.assertRaises(dw.Blocked):
            dw.validate(dict(rec, digest="e"), unit, Path("/r"), "/rep",
                        "d", True)
        with self.assertRaisesRegex(dw.Refusal, "not a fixed point.*"
                                    "re-primed or rebuilt"):
            dw.validate(dict(rec, churn=[".hol/make-deps/A.sig.d",
                                         "../../integer/.hol/make-deps/"
                                         "B.d"]),
                        unit, Path("/r"), "/rep", "d", False)

    def test_probe_facts_need_the_reporter_in_every_process(self):
        report = self.probe_report()
        full = self.probe_receipts()
        facts = dw.probe_facts(report, full)
        self.assertTrue(facts["ok"], facts)
        self.assertEqual(facts["heaps"], list(cases.HEAPS))
        self.assertEqual(
            facts["heap_anchors"]["base:" + cases.REALHEAP]["anchors"],
            sorted(REAL_DEPS))
        self.assertEqual(
            facts["heap_anchors"]["cand:" + cases.NUMHEAP]["anchors"],
            sorted(NUM_DEPS))
        unseen = self.probe_receipts(unseen=("rat", "base"))
        self.assertFalse(dw.probe_facts(report, unseen)["ok"])
        part = dict(report, workloads=["logroot"])
        one = [r for r in full if r["workload"] == "logroot"]
        self.assertTrue(dw.probe_facts(part, one)["ok"])
        self.assertFalse(dw.probe_facts(part, one)["complete"])

    def test_every_heap_must_positively_show_itself(self):
        report = self.probe_report()
        # the realheap unit shows a heap that differs from the others but
        # has none of the modules the realheap is built from
        for loaded in (["Lib", "Thm", "boss", "other"],
                       ["Lib", "Thm", "boss"] + REAL_DEPS[:1],
                       preloaded("bin/hol.state0")):
            got = dw.probe_facts(report, self.probe_receipts(
                loaded={"lim": loaded}))
            self.assertFalse(got["ok"], loaded)
        # a heap that does not contain the heap it was built on
        got = dw.probe_facts(report, self.probe_receipts(
            loaded={"lim": REAL_DEPS + ["Lib", "Thm"]}))
        self.assertFalse(got["ok"])
        # units of one heap that disagree
        got = dw.probe_facts(report, self.probe_receipts(
            loaded={"rich_list": preloaded("bin/hol.state0")}))
        self.assertFalse(got["ok"])
        # an anchor list that cannot be read from the heap's own build
        root = Path(report["roots"]["base"])
        (root / "src/real/analysis/Holmakefile").write_text("all:\n")
        got = dw.probe_facts(report, self.probe_receipts())
        self.assertFalse(got["ok"])

    def probe_report(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="t32-probe-"))
        self.addCleanup(shutil.rmtree, self.tmp, True)
        roots = {}
        for side in ("base", "cand"):
            roots[side] = str(self.tmp / side)
            for rel, text in HEAP_MAKEFILES.items():
                (self.tmp / side / rel).mkdir(parents=True)
                (self.tmp / side / rel / "Holmakefile").write_text(text)
        return dict(workloads=list(cases.NAMES), roots=roots, reporter={
            s: dict(dir="/rep-" + s) for s in ("base", "cand")})

    @staticmethod
    def probe_receipts(unseen=None, loaded=None):
        out = []
        for name in cases.NAMES:
            for side in ("base", "cand"):
                files = [] if unseen == (name, side) else [
                    ["T32Report.sml", "/rep-" + side]]
                modules = (loaded or {}).get(name) or preloaded(
                    cases.BY_NAME[name]["heap"])
                out.append(dict(workload=name, side=side, rewritten=[],
                                stats=dict(loaded_before=modules,
                                           loaded=[], files=files)))
        return out


class Refusals(Base):
    """Every per-process refusal, through the whole pipeline: the row is
    archived as rejected, the attempt closes failed (or blocked) and the
    snapshots are byte-identical afterwards (a stray file is moved to the
    evidence, not left)."""

    def attempt(self, kind, name="logroot", side=None, at=1, stage="first"):
        self.world.fault = lambda unit, s, n: (
            kind if n >= at and unit["name"] == name and
            side in (None, s) else None)
        before = self.world.snapshot()
        report = self.world.run("out-" + kind, self.world.spec(
            [name], stage=stage))
        self.assertFalse(report["success"], kind)
        self.assertEqual(self.world.snapshot(), before, kind)
        self.assertFalse(report["runs"][-1]["accepted"])
        return report

    def test_a_failed_process_is_refused(self):
        report = self.attempt("exit")
        self.assertIn("process failed: exit 1", report["failure"])

    def test_the_intermediates_of_a_failed_theory_are_moved_to_evidence(self):
        report = self.attempt("exit")
        label = report["runs"][-1]["receipt"][:-len(".json.gz")]
        receipt = a.load(Path(report["output"]) / report["runs"][-1][
            "receipt"])
        self.assertEqual(sorted(receipt["moved"]), sorted([
            ".hol/objs/logrootScript.uo", "logrootScript",
            ".hol/objs/part.dumpedheap"]))
        for rel in receipt["moved"]:
            self.assertTrue((Path(report["output"]) / "stray" / label /
                             "inside" / rel).is_file(), rel)

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

    def test_a_modified_existing_file_says_rebuild_and_stays(self):
        self.world.fault = lambda u, s, n: "modify"
        report = self.world.run("m", self.world.spec(["logroot"]))
        self.assertFalse(report["success"])
        self.assertIn("modified existing file(s) outside the products: "
                      "other.sml; the snapshot must be rebuilt",
                      report["failure"])
        folder = self.world.roots["base"] / "src/num/extra_theories"
        self.assertEqual((folder / "other.sml").read_text(), "val x = 2\n")

    def test_make_deps_churn_outside_the_target_fails_closed(self):
        report = self.attempt_nowrite("churn")
        self.assertIn("other.d", report["failure"])
        self.assertIn("must be rebuilt", report["failure"])

    def evidence(self, report):
        label = report["runs"][-1]["receipt"][:-len(".json.gz")]
        return Path(report["output"]) / "stray" / label

    def receipt_of(self, report):
        return a.load(Path(report["output"]) / report["runs"][-1][
            "receipt"])

    def test_new_make_deps_files_are_churn_removed_and_refused(self):
        report = self.attempt("cache")
        self.assertIn("not a fixed point", report["failure"])
        receipt = self.receipt_of(report)
        self.assertEqual(receipt["churn"], [
            ".hol/make-deps/FooTheory.sig.d",
            "sub/.hol/make-deps/B.sml.d"])
        self.assertEqual(receipt["stray"], [])

    def test_a_new_dot_hol_in_the_folder_is_stray_not_churn(self):
        report = self.attempt("newhol")
        self.assertIn("stray write: fresh/.hol/make-deps/C.d",
                      report["failure"])
        self.assertEqual(self.receipt_of(report)["churn"], [])

    def test_new_files_outside_make_deps_are_still_stray(self):
        self.assertIn("stray write: .hol/other.txt",
                      self.attempt("other")["failure"])
        self.assertIn("stray write: foo.d",
                      self.attempt("outsided")["failure"])

    def test_churn_in_another_directorys_make_deps_is_removed(self):
        report = self.attempt("xcache")
        self.assertIn("not a fixed point", report["failure"])
        receipt = self.receipt_of(report)
        self.assertEqual(receipt["churn"], [
            "../../integer/.hol/make-deps/IncTheory.sig.d"])
        self.assertEqual(receipt["stray"], [])
        self.assertGreater(receipt["scan_seconds"], 0)

    def test_a_make_deps_directory_the_process_made_is_removed(self):
        for side in self.world.roots.values():
            shutil.rmtree(side / "src/boss/.hol/make-deps")
        report = self.attempt("xnewdir")
        self.assertEqual(self.receipt_of(report)["churn"], [
            "../../boss/.hol/make-deps/BTheory.sml.d"])

    def test_another_directorys_non_cache_file_is_stray(self):
        report = self.attempt("xother")
        self.assertIn("stray write: ../../integer/.hol/make-deps/inc.txt",
                      report["failure"])
        self.assertTrue((self.evidence(report) / "outside" /
                         "src/integer/.hol/make-deps/inc.txt").is_file())

    def test_another_directorys_modified_cache_file_is_refused(self):
        self.world.fault = lambda u, s, n: "xmodify"
        report = self.world.run("x", self.world.spec(["logroot"]))
        self.assertFalse(report["success"])
        self.assertIn("modified existing file(s) outside the products: "
                      "../../integer/.hol/make-deps/other.d",
                      report["failure"])

    def test_a_new_directory_in_another_make_deps_is_stray(self):
        report = self.attempt("xsubdir")
        self.assertIn("stray write: ../../integer/.hol/make-deps/sub",
                      report["failure"])

    def test_a_new_dot_hol_in_a_directory_without_one_is_stray(self):
        report = self.attempt("xbare")
        self.assertIn("stray write: ../.hol", report["failure"])
        self.assertTrue((self.evidence(report) / "outside" /
                         "src/num/.hol/make-deps/x.d").is_file())

    def test_check_churn(self):
        one = dict(workload="u", side="base", churn=["a/.hol/make-deps/x.d"])
        two = dict(one, side="cand")
        dw.check_churn([one, two, dict(one, workload="v", churn=[])])
        dw.check_churn([])
        with self.assertRaisesRegex(dw.Refusal, "differs.*of: u"):
            dw.check_churn([one, dict(two, churn=[])])
        with self.assertRaisesRegex(dw.Refusal, "differs"):
            dw.check_churn([one, dict(one, churn=[])])

    def test_the_cache_predicate(self):
        yes = dw.is_holmake_cache
        self.assertTrue(yes(".hol/make-deps/XTheory.sig.d"))
        self.assertTrue(yes("a/.hol/make-deps/Y.d"))
        self.assertTrue(yes("../a/.hol/make-deps/Y.d"))
        self.assertFalse(yes("a/.hol/make-deps/x/Y.d"))
        self.assertFalse(yes("a/.hol/make-deps/x/.hol/make-deps/y/Y.d"))
        self.assertFalse(yes("make-deps/Y.d"))
        self.assertFalse(yes(".hol/make-deps/Y"))
        self.assertFalse(yes("foo.d"))
        self.assertFalse(yes(".hol/make-deps/x.txt"))
        self.assertFalse(yes(".hol/other/x.d"))
        self.assertFalse(yes(".hol/make-deps"))

    def attempt_nowrite(self, kind):
        self.world.fault = lambda u, s, n: kind
        report = self.world.run("c", self.world.spec(["logroot"]))
        self.assertFalse(report["success"])
        return report

    def test_the_targets_own_make_deps_are_rewritten_and_restored(self):
        before = self.world.snapshot()
        report = self.world.run("ok", self.world.spec(["logroot"]))
        self.assertTrue(report["success"])
        self.assertEqual(self.world.snapshot(), before)
        receipt = a.load(Path(report["output"]) / report["runs"][0][
            "receipt"])
        self.assertIn(".hol/make-deps/logrootTheory.sig.d",
                      receipt["rewritten"])

    def test_an_extension_module_is_refused(self):
        report = self.attempt("extension", side="base")
        self.assertIn("extension module(s) loaded: simpExt",
                      report["failure"])
        self.assertNotIn("blocked", report)

    def test_a_blocked_run_exits_2(self):
        blocked = self.attempt("extension", side="cand", name="logroot")
        self.assertIn("blocked", blocked)
        self.assertEqual(dw.exit_of(blocked), 2)

    def test_a_refused_run_exits_3(self):
        refused = self.attempt("exit")
        self.assertNotIn("blocked", refused)
        self.assertEqual(dw.exit_of(refused), 3)

    def test_a_loaded_path_outside_the_root_is_refused(self):
        self.assertIn("outside the root",
                      self.attempt("outside")["failure"])

    def test_a_process_running_in_another_root_is_refused(self):
        report = self.attempt("holdir", name="reduce-selftest")
        self.assertIn("runs in /elsewhere", report["failure"])

    def test_a_candidate_finding_blocks_and_is_judged(self):
        report = self.attempt("extension", side="cand")
        self.assertIn("blocked", report)
        self.assertEqual(self.world.status()[-1][1], ["blocked"])
        with self.assertRaisesRegex(dw.Refusal, "judged attempt"):
            self.world.run("again", self.world.spec(["logroot"]))

    def test_a_candidate_output_mismatch_is_a_finding_too(self):
        report = self.attempt("mismatch", side="cand")
        self.assertIn("blocked", report)

    def test_a_candidate_loading_a_new_module_is_blocked(self):
        self.world.fault = lambda u, s, n: "newstem" if s == "cand" else None
        report = self.world.run("n", self.world.spec(["logroot"]))
        self.assertFalse(report["success"])
        self.assertIn("candidate loaded what no baseline process loaded",
                      report["blocked"])
        self.assertIn("Zed", report["blocked"])

    def test_a_failure_before_any_measurement_is_void_and_may_be_redone(self):
        self.attempt("exit", at=1)
        found = dw.read_ledger(self.world.ledger())[1]
        (key,) = found
        self.assertIsNone(dw.judged_because(key[0], key[1], found[key]))
        self.world.fault = None
        report = self.world.run("redo", self.world.spec(["logroot"]))
        self.assertTrue(report["success"], report.get("failure"))

    def test_a_failure_after_admitted_processes_is_a_judged_draw(self):
        report = self.attempt("exit", at=6)
        self.assertGreater(len(report["runs"]), 1)
        found = dw.read_ledger(self.world.ledger())[1]
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
        with self.assertRaisesRegex(dw.Refusal, "needs the snapshot"):
            args, spec = self.world.info("n2", "smoke", no_verify=True)
            dw.run_stage(args, spec)  # not a subset: it feeds the counts

    def test_no_verify_is_for_an_information_subset_only(self):
        args, spec = self.world.info("s", "smoke", names=["logroot"],
                                     no_verify=True)
        report = dw.run_stage(args, spec)
        self.assertTrue(report["success"], report.get("failure"))
        self.assertNotIn("verify", report)

    def test_unauthorized_runs_do_not_start(self):
        with self.assertRaises(dw.Refusal):
            self.world.run("u", self.world.spec(["logroot"]),
                           authorize_measurements=False)
        self.assertFalse(self.world.calls)

    def test_the_ledger_must_be_ignored_by_git(self):
        (self.world.repo / ".gitignore").write_text("")
        with self.assertRaisesRegex(ValueError, "tracked by git"):
            self.world.run("i", self.world.spec(["logroot"]))
        self.assertFalse(self.world.calls)


class Manifest(Base):
    def load(self, **change):
        self.world.write_manifest(**change)
        return dw.load_manifest(self.world.manifest,
                                self.world.roots["base"],
                                self.world.roots["cand"])

    def test_a_complete_manifest_is_read(self):
        sides, seal = self.load()
        self.assertEqual(sides["base"]["pin"], self.world.base_pin)
        self.assertEqual(seal, a.seal(self.world.manifest))

    def test_wrong_schema_incomplete_or_mislabelled_sides_are_refused(self):
        for change, text in (
                (dict(schema="task32-independent-build-v1"), "not a snap"),
                (dict(cand=dict(incomplete=True)), "incomplete or mis"),
                (dict(base=dict(label="cand")), "incomplete or mis"),
                (dict(cand=dict(pin="abc")), "")):
            with self.assertRaisesRegex((dw.Refusal, ValueError), text):
                self.load(**change)
        data = json.loads(self.world.manifest.read_text())
        del data["sides"]["cand"]
        self.world.manifest.write_text(json.dumps(data))
        with self.assertRaisesRegex(dw.Refusal, "no complete base"):
            dw.load_manifest(self.world.manifest, self.world.roots["base"],
                             self.world.roots["cand"])

    def test_a_root_is_named_after_its_label(self):
        other = self.world.tmp / "other"
        other.mkdir()
        self.world.write_manifest(base=dict(root=str(other)))
        with self.assertRaisesRegex(dw.Refusal, "named after its label"):
            dw.load_manifest(self.world.manifest, other,
                             self.world.roots["cand"])

    def test_roots_must_be_the_given_ones_and_not_nested(self):
        with self.assertRaises(dw.Refusal):
            dw.load_manifest(self.world.manifest, self.world.roots["cand"],
                             self.world.roots["cand"])
        self.world.write_manifest()
        with self.assertRaises(dw.Refusal):
            self.world.run("m", self.world.spec(["logroot"]),
                           cand_root=self.world.tmp / "base")

    def test_the_gate_key_is_the_two_pins_only(self):
        sides, old = self.load()
        key = dw.gate_key(sides)
        self.world.manifest.write_text(self.world.manifest.read_text() +
                                       "\n")
        again, seal = dw.load_manifest(self.world.manifest,
                                       self.world.roots["base"],
                                       self.world.roots["cand"])
        self.assertEqual(dw.gate_key(again), key)
        self.assertNotEqual(seal, old)  # recorded beside, not in the key
        other = dict(sides, cand=dict(sides["cand"], pin="2" * 40))
        self.assertNotEqual(dw.gate_key(other), key)


class VerifyInterface(Base):
    def test_the_verify_argv_is_parsed_by_the_snapshots_own_parser(self):
        sides, _ = dw.load_manifest(self.world.manifest,
                                    self.world.roots["base"],
                                    self.world.roots["cand"])
        argv = dw.default_verify(self.world.repo, self.world.manifest, sides)
        self.assertEqual(Path(argv[2]).name, "task32_snapshots.py")
        seen = []

        def fake(manifest, base_pin, cand_pin, c31=None, probe=None,
                 poly=None):
            seen.append((manifest["schema"], base_pin, cand_pin, c31))
            return dict(status="pass")
        with mock.patch.object(snap, "verify", fake):
            self.assertEqual(snap.main(argv[3:]), 0)
        self.assertEqual(seen, [(snap.SCHEMA, self.world.base_pin,
                                 self.world.cand_pin, snap.C31)])
        self.assertEqual(argv[argv.index("--manifest") + 1],
                         str(self.world.manifest.resolve()))
        self.assertEqual(argv[argv.index("--repo") + 1],
                         str(self.world.repo.resolve()))

    def test_verify_inherits_the_serial_lock(self):
        child = [sys.executable, "-B", "-c", (
            "import sys; sys.path.insert(0, %r)\n"
            "import acceptance as a\n"
            "with a.serial_lock(sys.argv[1]): pass\n" % str(dw.HERE)),
            str(self.world.repo)]
        with a.serial_lock(self.world.repo) as fds:
            done = dw.run_verify(child, self.world.repo, fds)
            self.assertEqual(done["exit"], 0)
            self.assertGreaterEqual(done["seconds"], 0)
            bare = loading.execute(child, self.world.repo, dict(os.environ),
                                   60, fds)
            self.assertNotEqual(bare["exit"], 0)  # the lock is busy
            self.assertIn("lock busy", bare["stdout"])

    def test_the_verification_runs_before_and_after_a_stage(self):
        report = self.world.run("ok", self.world.spec(["logroot"]))
        for key in ("before", "after"):
            self.assertEqual(report["verify"][key]["exit"], 0)
            self.assertIn("seconds", report["verify"][key])


def pilot(world, names=("logroot",), name="pilot"):
    args, spec = world.info(name, "pilot", names=list(names))
    report = dw.run_stage(args, spec)
    assert report["success"], report.get("failure")
    return report


class Processes(Base):
    def test_theory_processes_restore_the_products_byte_for_byte(self):
        before = self.world.snapshot()
        report = self.world.run("ok", self.world.spec(["logroot"]))
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(self.world.snapshot(), before)
        self.assertEqual(len(report["runs"]), 40)
        self.assertEqual(report["outcome"]["digests"].keys(), {"logroot"})
        self.assertEqual(report["prebuilt"].keys(), {"logroot"})

    def test_commands_and_environment_of_the_units(self):
        self.world.run("c", self.world.spec(["logroot", "reduce-selftest"],
                                            pairs=10))
        theory = next(c for c in self.world.calls if c[0] == "logroot")
        env = theory[2]
        self.assertEqual(env["PATH"], snap.PATH)
        self.assertEqual((env["LC_ALL"], env["TZ"], env["TERM"]),
                         ("C", "UTC", "dumb"))
        self.assertTrue(env["POLY_CLINE_OPTIONS"].endswith("T32Report.uo"))
        self.assertNotIn("HOLSELFTESTLEVEL", env)
        self.assertTrue(env["HOME"].endswith("/home"))
        test = next(c for c in self.world.calls
                    if c[0] == "reduce-selftest")
        # exactly the build's recipe environment (S1's), nothing more
        # than the harness variables: no HOLSELFTESTLEVEL
        self.assertNotIn("HOLSELFTESTLEVEL", test[2])
        for call, extra in ((theory, {"T32_STATS", "T32_LAYOUT",
                                      "POLY_CLINE_OPTIONS"}),
                            (test, {"T32_STATS", "T32_LAYOUT"})):
            env = call[2]
            home = Path(env["HOME"])
            self.assertEqual(
                {k: v for k, v in env.items() if k not in extra},
                snap.environment(home, env["TMPDIR"]))
        self.assertNotIn("POLY_CLINE_OPTIONS", test[2])
        self.assertEqual({c[1] for c in self.world.calls}, {"base", "cand"})

    def test_the_selftest_command_puts_the_reporter_before_the_last_argument(
            self):
        root = self.world.roots["base"]
        unit = cases.BY_NAME["boss-selftest"]
        argv, cwd = dw.unit_argv(unit, root, "/rep/T32Report.uo")
        self.assertEqual(argv[-2:], ["/rep/T32Report.uo", "selftest"])
        self.assertEqual(argv[:3], [str(root / "bin/hol"),
                                    "--gcthreads=1", "run"])
        self.assertEqual(cwd, root / "src/boss")

    def test_a_theory_command_passes_no_prereqs(self):
        root = self.world.roots["base"]
        unit = cases.BY_NAME["logroot"]
        argv, cwd = dw.unit_argv(unit, root, "/rep/T32Report.uo")
        self.assertEqual(argv, [str(root / "bin/Holmake"), "--no-cache",
                                "--no_prereqs", "-j1", "logrootTheory.uo"])
        self.assertTrue(dw.unit_argv_shape(unit, root, "/rep/T32Report.uo",
                                           argv))
        self.assertFalse(dw.unit_argv_shape(
            unit, root, "/rep/T32Report.uo",
            [x for x in argv if x != "--no_prereqs"]))

    def test_scratch_is_removed_and_ledger_lines_are_chained(self):
        self.world.run("ok", self.world.spec(["logroot"]))
        self.assertFalse(list(self.world.tmp.glob("scratch/*")))
        self.assertFalse(list((self.world.repo / dw.JOURNALS).glob("*")))
        state = dw.tg.Ledger(self.world.ledger())
        self.assertEqual([r["event"] for r in state.records],
                         ["open", "close"])

    def test_selftests_compare_with_the_builds_own_normalized_log(self):
        unit = cases.BY_NAME["boss-selftest"]
        args, spec = self.world.info("s", "smoke", names=[unit["name"]])
        report = dw.run_stage(args, spec)
        self.assertTrue(report["success"], report.get("failure"))
        root = self.world.roots["base"]
        self.assertEqual(report["prebuilt"][unit["name"]],
                         dw.text_digest(BUILD_LOG.encode(), root))
        self.assertEqual(report["outcome"]["digests"][unit["name"]],
                         report["prebuilt"][unit["name"]])
        # a live output that differs from the build's log is refused
        self.world.fault = lambda u, s, n: "mismatch"
        args, spec = self.world.info("s2", "smoke", names=[unit["name"]])
        self.assertFalse(dw.run_stage(args, spec)["success"])

    def test_smoke_runs_both_sides_and_records_probe_and_overheads(self):
        args, spec = self.world.info("s", "smoke",
                                     names=["logroot", "boss-selftest"])
        report = dw.run_stage(args, spec)
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(len(report["runs"]), 4)
        out = report["outcome"]
        self.assertEqual(sorted(out["digests"]),
                         ["boss-selftest", "logroot"])
        self.assertTrue(out["probe"]["ok"])
        self.assertFalse(out["probe"]["complete"])
        self.assertEqual(out["probe"]["units"]["logroot"]["base"][
            "stats_lines"], 1)
        self.assertEqual(sorted(out["overheads"]["scan_seconds"]),
                         ["boss-selftest", "logroot"])
        self.assertEqual(sorted(out["overheads"]["verify_seconds"]),
                         ["after", "before"])

    def test_a_subset_may_be_measured_in_information_runs_only(self):
        args = self.world.args("o", only=["logroot"])
        self.assertEqual(dw.info_spec(args, "smoke")["names"], ["logroot"])

    def test_a_smoke_that_misses_the_reporter_fails_the_probe(self):
        self.world.fault = lambda u, s, n: "noreporter"
        args, spec = self.world.info("s", "smoke", names=["logroot"])
        report = dw.run_stage(args, spec)
        self.assertTrue(report["success"])
        self.assertFalse(report["outcome"]["probe"]["ok"])


class NegativeControl(Base):
    def control(self, name="ctl"):
        pilot(self.world)
        args, spec = self.world.info(name, "control",
                                     pilot=self.world.tmp / "pilot")
        return args, spec, dw.run_stage(args, spec)

    def test_the_busy_time_is_six_percent_of_the_pilots_whole_tree_cpu(self):
        args, spec, report = self.control()
        pilot_report = a.load(self.world.tmp / "pilot/downstream.json")
        cpu = pilot_report["outcome"]["pilot"]["logroot"]["median_cpu"]
        self.assertEqual(spec["busy"]["seconds"], round(0.06 * cpu, 6))
        self.assertEqual(spec["busy"]["median_cpu"], cpu)
        # the whole tree: wait4 CPU, about the unit's serial time
        self.assertAlmostEqual(cpu, cases.BY_NAME["logroot"]["serial"],
                               delta=0.5)
        self.assertTrue(report["success"], report.get("failure"))

    def test_the_negative_control_detects_the_busy_reporter(self):
        args, spec, report = self.control()
        self.assertTrue(report["success"], report.get("failure"))
        control = report["outcome"]["negative_control"]
        self.assertTrue(control["detected"], control)
        self.assertEqual(control["unit"], "logroot")
        busy = [c for c in self.world.calls if "T32_BUSY" in c[2]]
        self.assertEqual(len(busy), 10)
        self.assertEqual({float(c[2]["T32_BUSY"]) for c in busy},
                         {spec["busy"]["seconds"]})
        control_calls = self.world.calls[40:]  # after the pilot
        self.assertEqual({c[1] for c in control_calls}, {"base"})
        infos = dw.tg.Ledger(self.world.ledger()).records
        self.assertEqual([r["event"] for r in infos],
                         ["info", "info-end"] * 2)
        self.assertEqual(dw.exit_of(report), 0)
        # and the replay recomputes the busy time from the pilot's CPU
        info, again = dw.replay_one(self.world.tmp / "ctl")
        self.assertEqual(dw.dumps(again), dw.dumps(report))

    def test_the_negative_control_is_missed_without_the_busy_loop(self):
        pilot(self.world)
        self.world.ignore_busy = True
        args, spec = self.world.info("n", "control",
                                     pilot=self.world.tmp / "pilot")
        report = dw.run_stage(args, spec)
        self.assertTrue(report["success"])
        found = report["outcome"]["negative_control"]
        self.assertFalse(found["detected"])
        self.assertEqual(dw.exit_of(report), 1)

    def test_a_forged_busy_time_does_not_replay(self):
        args, spec, report = self.control()
        path = self.world.tmp / "ctl/downstream.json"
        forged = a.load(path)
        forged["busy"]["seconds"] *= 0.5
        path.write_text(json.dumps(forged))
        with self.assertRaises(dw.Refusal):
            dw.replay_one(self.world.tmp / "ctl")

    def test_a_control_needs_a_pilot_of_this_gate(self):
        args = self.world.args("c", pilot=self.world.tmp / "missing")
        with self.assertRaises(OSError):
            dw.info_spec(args, "control")


class Journal(Base):
    """The restore journal, recovery, kill and signal handling."""

    def test_the_journal_and_backups_exist_before_a_product_is_deleted(self):
        seen = []
        real = self.world.launch

        def check(argv, cwd, env, timeout, out, fds=()):
            (folder,) = dw.pending_journals(self.world.repo)
            entry = dw.journal_read(folder)["pending"]
            seen.append((entry["unit"], sorted(entry["meta"])))
            for rel in entry["meta"]:
                self.assertTrue((Path(entry["store"]) / rel).is_file())
                self.assertFalse((Path(entry["folder"]) / rel).exists())
            return real(argv, cwd, env, timeout, out, fds)
        with mock.patch.object(dw, "launch", check):
            report = self.world.run("j", self.world.spec(["logroot"]))
        self.assertTrue(report["success"])
        self.assertEqual(seen[0][0], "logroot")
        self.assertIn(".hol/make-deps/logrootTheory.sig.d", seen[0][1])
        self.assertEqual(dw.pending_journals(self.world.repo), [])

    def fatal(self):
        before = self.world.snapshot()
        with mock.patch.object(dw, "restore", lambda *x, **k: None):
            report = self.world.run("f", self.world.spec(["logroot"]))
        return before, report

    def test_a_failed_restore_is_fatal_and_keeps_backups_and_journal(self):
        before, report = self.fatal()
        self.assertFalse(report["success"])
        self.assertIn("Fatal: could not restore the products of logroot",
                      report["failure"])
        (folder,) = dw.pending_journals(self.world.repo)
        self.assertEqual(report["journal"], str(folder))
        self.assertTrue(str(folder).startswith(str(
            self.world.repo / ".agent-files/scratch/task32")))
        entry = dw.journal_read(folder)["pending"]
        self.assertTrue(entry["meta"])
        for rel, meta in entry["meta"].items():
            data = (Path(entry["store"]) / rel).read_bytes()
            self.assertEqual(dw.sha(data), meta["sha256"])
        self.assertIn(str(folder), report["failure"])

    def test_a_pending_journal_blocks_new_runs_until_recover(self):
        before, report = self.fatal()
        with self.assertRaisesRegex(dw.Refusal, "restore journal is pend"):
            self.world.run("g", self.world.spec(["logroot"]))
        self.assertEqual(dw.recover(self.world.repo), 0)
        self.assertEqual(self.world.snapshot(), before)
        self.assertEqual(dw.pending_journals(self.world.repo), [])
        report = self.world.run("h", self.world.spec(["logroot"]))
        self.assertTrue(report["success"], report.get("failure"))

    def test_recover_moves_the_files_the_killed_process_left(self):
        before, report = self.fatal()
        folder = self.world.roots["base"] / "src/num/extra_theories"
        (folder / ".hol/objs/leftover.uo").write_text("x")
        main = dw.main(["recover", "--repo", str(self.world.repo)])
        self.assertEqual(main, 0)
        self.assertEqual(self.world.snapshot(), before)
        kept = list((self.world.repo / dw.JOURNALS).glob(
            "*/strays/inside/.hol/objs/leftover.uo"))
        self.assertEqual(len(kept), 1)

    def test_recover_removes_cache_churn_in_other_directories(self):
        before, report = self.fatal()
        deps = self.world.roots["base"] / "src/integer/.hol/make-deps"
        (deps / "IncTheory.sig.d").write_text("d\n")
        (deps / "inc.txt").write_text("x")
        self.assertEqual(dw.recover(self.world.repo), 0)
        self.assertEqual(self.world.snapshot(), before)
        kept = list((self.world.repo / dw.JOURNALS).glob(
            "*/strays/outside/src/integer/.hol/make-deps/inc.txt"))
        self.assertEqual(len(kept), 1)

    def test_recover_refuses_an_untrustworthy_journal(self):
        self.fatal()
        (folder,) = dw.pending_journals(self.world.repo)
        good = dw.journal_read(folder)
        leftover = self.world.roots["base"] / "src/num/extra_theories/x.txt"
        leftover.write_text("x")

        def outside(**change):
            def edit(data):
                data["pending"]["outside"].update(change)
            return edit

        def entry(**change):
            def edit(data):
                data["pending"].update(change)
            return edit

        def bad_meta(key, value):
            def edit(data):
                meta = data["pending"]["meta"]
                meta[sorted(meta)[0]][key] = value
            return edit

        def drop(key):
            def edit(data):
                del data["pending"][key]
            return edit
        for edit, text in (
                (outside(root=str(self.world.tmp / "elsewhere")), "disagree"),
                (outside(dirs=["../x"]), "bad directory"),
                (outside(dirs=["/etc"]), "bad directory"),
                (outside(bare=["a/./b"]), "bad directory"),
                (outside(before={"x/.hol/make-deps/a.d": ["f", 1, 2]}),
                 "bad listing"),
                (drop("outside"), "malformed"),
                (drop("store"), "malformed"),
                (entry(store="/tmp/elsewhere"), "backup directory"),
                (entry(meta={"../x": {}}), "not the theory's"),
                (entry(unit="arithmetic"), "disagree"),
                (entry(unit="nowhere"), "disagree"),
                (entry(folder="/tmp/elsewhere"), "disagree"),
                (entry(stops=["x"]), "disagree"),
                (lambda d: d["pending"].update(
                    store=d["pending"]["store"] + "/../x"), "normalized"),
                (entry(folder="rel/path"), "normalized"),
                (outside(dirs="abc"), "malformed"),
                (outside(before=[]), "malformed"),
                (bad_meta("sha256", "XYZ"), "bad product record"),
                (bad_meta("mode", "x"), "bad product record"),
                (bad_meta("mtime_ns", 1.5), "bad product record"),
                (bad_meta("sha256", "0" * 64), "missing or changed"),
                (lambda d: d.update(schema="task32-journal-v1"),
                 "not of schema")):
            data = json.loads(json.dumps(good))
            edit(data)
            dw.journal_write(folder, data)
            with self.assertRaisesRegex(dw.Refusal, text):
                dw.recover(self.world.repo)
            # nothing was changed before the refusal
            self.assertTrue(leftover.exists(), text)
        dw.journal_write(folder, good)
        self.assertEqual(dw.recover(self.world.repo), 0)
        self.assertFalse(leftover.exists())

    def test_recover_removes_the_directories_the_process_made(self):
        before, report = self.fatal()
        folder = self.world.roots["base"] / "src/num/extra_theories"
        (folder / "fresh/.hol/make-deps").mkdir(parents=True)
        (folder / "fresh/.hol/make-deps/C.d").write_text("d\n")
        self.assertEqual(dw.recover(self.world.repo), 0)
        self.assertEqual(self.world.snapshot(), before)
        self.assertEqual(len(list((self.world.repo / dw.JOURNALS).glob(
            "*/strays/inside/fresh/.hol/make-deps/C.d"))), 1)

    def test_recover_removes_in_folder_cache_churn(self):
        before, report = self.fatal()
        folder = self.world.roots["base"] / "src/num/extra_theories"
        (folder / ".hol/make-deps/XTheory.sig.d").write_text("d\n")
        self.assertEqual(dw.recover(self.world.repo), 0)
        self.assertEqual(self.world.snapshot(), before)
        self.assertEqual(list((self.world.repo / dw.JOURNALS).rglob(
            "XTheory.sig.d")), [])

    def test_a_failing_settle_does_not_mask_a_fatal_restore(self):
        def boom(*args):
            raise RuntimeError("boom")
        with mock.patch.object(dw, "settle_outside", boom):
            before, report = self.fatal()
        self.assertIn("Fatal: could not restore the products of logroot",
                      report["failure"])
        self.assertIn("(also: RuntimeError: boom)", report["failure"])
        self.assertEqual(len(dw.pending_journals(self.world.repo)), 1)
        self.assertEqual(dw.recover(self.world.repo), 0)
        self.assertEqual(self.world.snapshot(), before)

    def test_a_failing_settle_is_a_note_on_the_signal(self):
        def boom(*args):
            raise RuntimeError("boom")
        self.world.fault = lambda u, s, n: "terminate"
        before = self.world.snapshot()
        with mock.patch.object(dw, "settle_outside", boom):
            with self.assertRaises(snap.Terminated) as caught:
                self.world.run("t", self.world.spec(["logroot"]))
        self.assertTrue(any("boom" in n for n in
                            caught.exception.__notes__))
        # the journal stays for `recover`, which puts everything back
        self.assertEqual(len(dw.pending_journals(self.world.repo)), 1)
        self.assertEqual(dw.recover(self.world.repo), 0)
        self.assertEqual(self.world.snapshot(), before)

    def test_a_failing_settle_alone_is_the_error_and_keeps_the_journal(self):
        def boom(*args):
            raise RuntimeError("boom")
        with mock.patch.object(dw, "settle_outside", boom):
            report = self.world.run("b", self.world.spec(["logroot"]))
        self.assertFalse(report["success"])
        self.assertIn("RuntimeError: boom", report["failure"])
        self.assertEqual(len(dw.pending_journals(self.world.repo)), 1)

    def test_recover_with_nothing_pending_is_a_noop(self):
        self.assertEqual(dw.recover(self.world.repo), 0)

    def test_an_unreadable_journal_counts_as_pending(self):
        folder = self.world.repo / dw.JOURNALS / "x"
        folder.mkdir(parents=True)
        (folder / "journal.json").write_text("{")
        self.assertEqual(dw.pending_journals(self.world.repo), [folder])

    def test_a_signal_restores_closes_the_attempt_and_leaves_no_journal(self):
        self.world.fault = lambda u, s, n: "terminate" if n >= 3 else None
        before = self.world.snapshot()
        with self.assertRaises(snap.Terminated) as caught:
            self.world.run("t", self.world.spec(["logroot"]))
        # raised again after the close; it carries the saved report
        self.assertTrue(caught.exception.saved)
        report = a.load(self.world.tmp / "t" / "downstream.json")
        self.assertEqual(report, json.loads(dw.dumps(
            caught.exception.report)))
        self.assertFalse(report["success"])
        self.assertIn("Terminated: SIGTERM", report["failure"])
        self.assertEqual(self.world.snapshot(), before)
        self.assertEqual(dw.pending_journals(self.world.repo), [])
        status = self.world.status()
        self.assertEqual(status[-1][1], ["failed"])
        self.assertEqual(report["runs"][-1]["accepted"], True)


class Launch(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory(prefix="t32-launch-")
        self.addCleanup(self.dir.cleanup)
        self.tmp = Path(self.dir.name)

    def test_a_process_that_ends_in_time_is_not_timed_out(self):
        got = dw.launch(["true"], self.tmp, dict(os.environ), 30,
                        self.tmp / "o")
        self.assertEqual((got["exit"], got["timed_out"]), (0, False))
        self.assertGreater(got["wall"], 0)

    def test_the_deadline_kills_the_whole_group(self):
        pidfile = self.tmp / "pid"
        got = dw.launch(["sh", "-c", "echo $$ > %s; sleep 30 & wait" %
                         pidfile], self.tmp, dict(os.environ), 0.5,
                        self.tmp / "o")
        self.assertEqual((got["exit"], got["timed_out"]), (-9, True))
        self.assertEqual(dw.group_members(int(pidfile.read_text())), [])

    def test_a_signal_kills_the_group_and_waits_for_it(self):
        pidfile = self.tmp / "pid"
        timer = threading.Timer(0.5, os.kill, (os.getpid(), signal.SIGTERM))
        with snap.terminating():
            timer.start()
            with self.assertRaises(snap.Terminated):
                dw.launch(["sh", "-c", "echo $$ > %s; sleep 30" % pidfile],
                          self.tmp, dict(os.environ), 60, self.tmp / "o")
        timer.cancel()
        self.assertEqual(dw.group_members(int(pidfile.read_text())), [])

    def test_a_group_left_behind_by_the_leader_is_killed_and_recorded(self):
        pidfile = self.tmp / "pid"
        got = dw.launch(["sh", "-c", "echo $$ > %s; sleep 30 &" % pidfile],
                        self.tmp, dict(os.environ), 30, self.tmp / "o")
        self.assertEqual((got["exit"], got["timed_out"]), (0, False))
        # the backgrounded child may still be the forked sh before its exec
        self.assertTrue(got["survivors"])
        self.assertLessEqual(set(got["survivors"]), {"sh", "sleep"})
        self.assertEqual(dw.group_members(int(pidfile.read_text())), [])
        clean = dw.launch(["true"], self.tmp, dict(os.environ), 30,
                          self.tmp / "o")
        self.assertEqual(clean["survivors"], [])
        usage = dict(exit=0, timed_out=False, survivors=["sleep"])
        with self.assertRaisesRegex(dw.Refusal, "running descendants: "
                                    "sleep"):
            dw.validate(dict(usage=usage, stats=None, modified=[],
                             stray=[], digest="d"),
                        cases.BY_NAME["logroot"], Path("/r"), "/rep", "d",
                        False)

    def test_signals_follow_the_shared_state_machine(self):
        term = signal.SIGTERM
        # DEFER records, the end of the block raises
        seen = []
        with snap.terminating():
            with self.assertRaises(snap.Terminated):
                with snap.deferred():
                    os.kill(os.getpid(), term)
                    time.sleep(0.05)
                    seen.append("finished")
        self.assertEqual(seen, ["finished"])
        # a burst raises at most once
        with snap.terminating():
            with self.assertRaises(snap.Terminated):
                os.kill(os.getpid(), term)
                time.sleep(0.05)
            os.kill(os.getpid(), term)
            time.sleep(0.05)  # recorded only: no second raise
            self.assertEqual(snap.STATE.mode, snap.DEFER)
            self.assertEqual(len(snap.STATE.recorded), 2)
        # a signal recorded outside a wait is raised at its entry
        with snap.terminating(snap.DEFER):
            os.kill(os.getpid(), term)
            time.sleep(0.05)
            with self.assertRaises(snap.Terminated):
                with snap.raising():
                    seen.append("not reached")
        self.assertEqual(seen, ["finished"])
        # a block that ends with an error keeps it as the primary error
        with snap.terminating():
            with self.assertRaises(dw.Fatal) as caught:
                with snap.deferred():
                    os.kill(os.getpid(), term)
                    time.sleep(0.05)
                    raise dw.Fatal("restore failed")
        self.assertEqual(str(caught.exception), "restore failed")
        self.assertIn("SIGTERM", caught.exception.__notes__[0])
        # recorded and never raised: raised when the guard ends
        with self.assertRaises(snap.Terminated):
            with snap.terminating(snap.DEFER):
                os.kill(os.getpid(), term)
                time.sleep(0.05)
        self.assertEqual(snap.STATE.mode, snap.RAISE)

    def test_a_signal_during_a_failed_restore_keeps_the_fatal(self):
        (self.tmp / "w").mkdir()
        world = World(self.tmp / "w")
        for patch in world.patches():
            patch.start()
            self.addCleanup(patch.stop)

        def settle(*args, **kw):
            os.kill(os.getpid(), signal.SIGTERM)
            time.sleep(0.05)
            return dict(ok=False, moved=[], churn=[], modified=[],
                        rewritten=[])
        with mock.patch.object(dw, "settle", settle):
            report = world.run("x", world.spec(["logroot"]))
        self.assertFalse(report["success"])
        self.assertTrue(report["failure"].startswith("Fatal: could not "
                                                     "restore"))
        self.assertIn("SIGTERM", report["failure"])
        self.assertTrue(report.get("journal"))
        for lock in Path(world.repo, ".agent-files").glob("*.lock"):
            lock.unlink()

    def test_a_signal_during_the_restore_does_not_cut_it_short(self):
        (self.tmp / "w").mkdir()
        world = World(self.tmp / "w")
        for patch in world.patches():
            patch.start()
            self.addCleanup(patch.stop)
        real = dw.settle
        done = []

        def settle(*args, **kw):
            os.kill(os.getpid(), signal.SIGTERM)  # a second signal
            got = real(*args, **kw)
            done.append(got["ok"])
            return got
        with mock.patch.object(dw, "settle", settle):
            before = world.snapshot()
            with snap.terminating():
                try:
                    world.run("x", world.spec(["logroot"]))
                except snap.Terminated:
                    pass
        self.assertEqual(done and set(done), {True})
        self.assertEqual(world.snapshot(), before)
        for lock in Path(world.repo, ".agent-files").glob("*.lock"):
            lock.unlink()

    def test_handlers_do_not_override_an_ignored_signal(self):
        old = signal.signal(signal.SIGHUP, signal.SIG_IGN)
        try:
            with snap.terminating():
                self.assertEqual(signal.getsignal(signal.SIGHUP),
                                 signal.SIG_IGN)
                self.assertNotEqual(signal.getsignal(signal.SIGTERM),
                                    signal.SIG_IGN)
        finally:
            signal.signal(signal.SIGHUP, old)


class Unsaved(Base):
    """A report that cannot be saved still closes the attempt, with no seal,
    and the chained ledger stays readable."""

    def judged_closes(self):
        found = dw.read_ledger(self.world.ledger())[1]
        why = dw.reasons(found)
        return found, why

    def test_a_failed_save_closes_unsealed_and_counts_as_judged(self):
        w = self.world
        real = a.save

        def save(path, data, *rest):
            if Path(path).name == "downstream.json":
                raise OSError("disk full")
            return real(path, data, *rest)
        w.fault = lambda u, s, n: "exit"
        with mock.patch.object(a, "save", save):
            with self.assertRaisesRegex(OSError, "disk full"):
                w.run("x", w.spec(["logroot"]))
        found, why = self.judged_closes()
        (key, row), = found.items()
        self.assertIsNone(row["closes"][0]["seal"])
        self.assertIn("no seal", why[key])
        self.assertIsNotNone(why[key])  # judged, not void

    def test_a_signal_during_the_save_lets_it_and_the_close_finish(self):
        w = self.world
        real = a.save
        seen = []

        def save(path, data, *rest):
            if Path(path).name == "downstream.json":
                os.kill(os.getpid(), signal.SIGTERM)
                time.sleep(0.05)
                seen.append("saving")
            return real(path, data, *rest)
        with mock.patch.object(a, "save", save):
            with self.assertRaises(snap.Terminated):
                w.run("x", w.spec(["logroot"]))
        self.assertEqual(seen, ["saving"])
        self.assertTrue((w.tmp / "x" / "downstream.json").is_file())
        found, why = self.judged_closes()
        (key, row), = found.items()
        self.assertEqual(len(row["closes"]), 1)
        self.assertEqual(row["closes"][0]["seal"],
                         a.seal(w.tmp / "x" / "downstream.json")["sha256"])
        self.assertIsNotNone(why[key])  # judged, not void


    def cli(self, name, hook):
        """`main` of a smoke run of logroot with `hook` replacing a.save;
        returns (exit status, stdout, stderr)."""
        w = self.world
        argv = ["smoke", "--repo", str(w.repo), "--base-root",
                str(w.roots["base"]), "--cand-root", str(w.roots["cand"]),
                "--manifest", str(w.manifest), "--output",
                str(w.tmp / name), "--scratch", str(w.tmp / "scratch"),
                "--verify-argv", "%s -c pass" % sys.executable,
                "--authorize-measurements", "--only", "logroot"]
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(sys, "stdout", out), \
                mock.patch.object(sys, "stderr", err), hook:
            code = dw.main(argv)
        return code, out.getvalue(), err.getvalue()

    def test_a_signal_during_the_save_exits_4_with_the_summary(self):
        real = a.save

        def save(path, data, *rest):
            if Path(path).name == "downstream.json":
                os.kill(os.getpid(), signal.SIGTERM)
                time.sleep(0.05)
            return real(path, data, *rest)
        code, out, err = self.cli("x", mock.patch.object(a, "save", save))
        self.assertEqual(code, dw.TERMINATED)
        self.assertEqual(dw.TERMINATED, 4)
        self.assertIn("TERMINATED by SIGTERM", err)
        self.assertIn("TASK32 smoke: attempt", out)
        self.assertIn("success True", out)
        self.assertIn("the result is recorded", out)
        self.assertTrue((self.world.tmp / "x/downstream.json").is_file())

    def test_a_signal_with_an_attempt_that_cannot_close_says_so(self):
        real = a.save

        def save(path, data, *rest):
            if Path(path).name == "downstream.json":
                os.kill(os.getpid(), signal.SIGTERM)
                time.sleep(0.05)
            return real(path, data, *rest)

        append = dw.tg.ledger_append

        def broken(path, **record):
            if record["event"] in ("info-end", "close"):
                raise OSError("ledger unwritable")
            return append(path, **record)
        with mock.patch.object(dw.tg, "ledger_append", broken):
            code, out, err = self.cli("x", mock.patch.object(
                a, "save", save))
        self.assertEqual(code, 4)
        self.assertIn("ATTEMPT-NOT-CLOSED", err)
        self.assertNotIn("is closed", out)
        self.assertNotIn("the result is recorded", out)
        self.assertIn("no report was saved", out)
        self.assertIn("(R-1)", out)

    def test_a_signal_noted_on_another_failure_keeps_exit_3(self):
        real = a.save

        def save(path, data, *rest):
            if Path(path).name == "downstream.json":
                os.kill(os.getpid(), signal.SIGTERM)
                time.sleep(0.05)
                raise OSError("disk full")
            return real(path, data, *rest)
        code, out, err = self.cli("x", mock.patch.object(a, "save", save))
        self.assertEqual(code, 3)
        self.assertIn("REFUSED", err)
        self.assertIn("SIGTERM", err)

    def test_a_signal_during_the_body_exits_4(self):
        w = self.world
        real = dw.run_verify
        calls = []

        def verify(*args, **kw):
            calls.append(1)
            os.kill(os.getpid(), signal.SIGTERM)
            time.sleep(0.05)
            return real(*args, **kw)
        code, out, err = self.cli("y", mock.patch.object(
            dw, "run_verify", verify))
        self.assertEqual(code, 4)
        self.assertIn("TERMINATED by SIGTERM", err)
        # the body's signal is a failed stage, saved and closed
        self.assertIn("success False", out)
        self.assertIn("the result is recorded", out)
        saved = a.load(self.world.tmp / "y" / "downstream.json")
        self.assertIn("Terminated: SIGTERM", saved["failure"])
        state = dw.tg.Ledger(self.world.ledger())
        ends = [r for r in dw.table_lines(state)
                if r["event"] == "info-end"]
        self.assertEqual([r["success"] for r in ends], [False])

    def test_any_other_exception_is_exit_3_not_a_traceback(self):
        def explode(*args, **kw):
            raise KeyError("malformed")
        code, out, err = self.cli("k", mock.patch.object(
            dw, "info_spec", explode))
        self.assertEqual(code, 3)
        self.assertIn("REFUSED: KeyError", err)

    def test_a_malformed_counts_file_exits_3(self):
        w = self.world
        bad = w.tmp / "bad-counts.json"
        bad.write_text("[]")
        out, err = io.StringIO(), io.StringIO()
        with mock.patch.object(sys, "stderr", err), \
                mock.patch.object(sys, "stdout", out):
            code = dw.main([
                "run", "--repo", str(w.repo), "--base-root",
                str(w.roots["base"]), "--cand-root", str(w.roots["cand"]),
                "--manifest", str(w.manifest), "--counts", str(bad),
                "--output", str(w.tmp / "bad-run"), "--scratch",
                str(w.tmp / "scratch"), "--verify-argv",
                "%s -c pass" % sys.executable,
                "--authorize-measurements", "--only", "logroot"])
        self.assertEqual(code, 3)
        self.assertIn("AttributeError", err.getvalue())
        self.assertNotIn("Traceback", err.getvalue())

    def test_a_keyboard_interrupt_propagates_out_of_main(self):
        def interrupt(*args, **kw):
            raise KeyboardInterrupt
        with mock.patch.object(dw, "dispatch", interrupt), \
                self.assertRaises(KeyboardInterrupt):
            dw.main(["recover", "--repo", str(self.world.repo)])

    def test_any_exception_in_the_body_is_recorded_as_a_failure(self):
        def explode(*args, **kw):
            raise RuntimeError("boom")
        code, out, err = self.cli("rt", mock.patch.object(
            dw, "run_verify", explode))
        self.assertEqual(code, 3)
        self.assertIn("failure: RuntimeError: boom", out)
        saved = a.load(self.world.tmp / "rt" / "downstream.json")
        self.assertIn("RuntimeError: boom", saved["failure"])
        state = dw.tg.Ledger(self.world.ledger())
        ends = [r for r in dw.table_lines(state)
                if r["event"] == "info-end"]
        self.assertEqual([r["success"] for r in ends], [False])

    def test_a_keyboard_interrupt_in_the_body_still_closes_the_attempt(self):
        def interrupt(*args, **kw):
            raise KeyboardInterrupt
        with self.assertRaises(KeyboardInterrupt):
            self.cli("ki", mock.patch.object(dw, "run_verify", interrupt))
        state = dw.tg.Ledger(self.world.ledger())
        ends = [r for r in dw.table_lines(state)
                if r["event"] == "info-end"]
        self.assertEqual([r["success"] for r in ends], [False])

    def test_a_relative_scratch_is_resolved_for_the_children(self):
        w = self.world
        parsed = dw.build_parser().parse_args([
            "smoke", "--repo", "r", "--base-root", "b", "--cand-root",
            "c", "--manifest", "m", "--output", "o", "--scratch", "rel"])
        self.assertEqual(parsed.scratch, Path(os.getcwd()) / "rel")
        seen = []
        real = dw.process_env

        def spy(scratch, extra):
            env = real(scratch, extra)
            seen.append((env["HOME"], env["TMPDIR"]))
            return env
        here = os.getcwd()
        os.chdir(w.tmp)
        try:
            argv = ["smoke", "--repo", str(w.repo), "--base-root",
                    str(w.roots["base"]), "--cand-root",
                    str(w.roots["cand"]), "--manifest", str(w.manifest),
                    "--output", "rel-out", "--scratch", "rel-scratch",
                    "--verify-argv", "%s -c pass" % sys.executable,
                    "--authorize-measurements", "--only", "logroot"]
            with mock.patch.object(dw, "process_env", spy), \
                    mock.patch.object(sys, "stdout", io.StringIO()), \
                    mock.patch.object(sys, "stderr", io.StringIO()):
                dw.main(argv)
        finally:
            os.chdir(here)
        self.assertTrue(seen)
        for home, tmp in seen:
            self.assertTrue(os.path.isabs(home) and os.path.isabs(tmp))
            self.assertTrue(home.startswith(str(w.tmp / "rel-scratch")))

    def test_a_signal_before_any_report_prints_what_is_left(self):
        def terminate(*args, **kw):
            raise snap.Terminated("SIGHUP")
        code, out, err = self.cli("z", mock.patch.object(
            dw, "info_spec", terminate))
        self.assertEqual(code, 4)
        self.assertIn("TERMINATED by SIGHUP", err)
        self.assertIn("no report was saved", out)
        self.assertIn("(R-1)", out)

    def test_a_signal_at_the_entry_of_the_deferred_close_still_closes(self):
        w = self.world
        real = snap.deferred

        @contextlib.contextmanager
        def entering(*args, **kw):
            # the signal arrives as the close's deferred block is entered
            if sys._getframe(2).f_code.co_name == "run_stage":
                os.kill(os.getpid(), signal.SIGTERM)
                time.sleep(0.05)
            with real(*args, **kw):
                yield
        with mock.patch.object(snap, "deferred", entering):
            with self.assertRaises(snap.Terminated):
                w.run("x", w.spec(["logroot"]))
        self.assertTrue((w.tmp / "x" / "downstream.json").is_file())
        found, _ = self.judged_closes()
        (key, row), = found.items()
        self.assertEqual(row["closes"][0]["seal"],
                         a.seal(w.tmp / "x" / "downstream.json")["sha256"])

    def test_a_signal_as_the_hold_is_made_still_closes(self):
        w = self.world
        real = snap.hold
        calls = []

        def hold():
            # the first call is the end of the body's try: the signal
            # raises there, inside the try, so the finally runs
            calls.append(1)
            if len(calls) == 1:
                os.kill(os.getpid(), signal.SIGTERM)
                time.sleep(0.05)
            real()
        with mock.patch.object(snap, "hold", hold):
            with self.assertRaises(snap.Terminated):
                w.run("x", w.spec(["logroot"]))
        report = a.load(w.tmp / "x" / "downstream.json")
        self.assertFalse(report["success"])
        self.assertTrue(report["failure"].startswith("Terminated"))
        found, _ = self.judged_closes()
        (key, row), = found.items()
        self.assertEqual(len(row["closes"]), 1)
        self.assertIsNotNone(row["closes"][0]["seal"])


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
                                    ledger=self.world.ledger())
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
        ledger = self.world.ledger()
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
            dw.replay_one(folder, ledger=self.world.ledger())

    def test_replay_checks_the_ledger_close_and_the_draw_count(self):
        self.stage()
        folder = self.world.tmp / "r"
        ledger = self.world.ledger()
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
        dw.replay_one(self.world.tmp / "r", ledger=self.world.ledger())
        self.assertEqual(len(self.world.calls), calls)

    def test_a_pass_replays_as_a_pass(self):
        self.stage(scale=1.0, name="p")
        info, _ = dw.replay_one(self.world.tmp / "p",
                                ledger=self.world.ledger())
        self.assertEqual(info["exit"], "pass")

    def test_an_information_run_replays_against_the_prebuilt_digest(self):
        args, spec = self.world.info("s", "smoke", names=["logroot"])
        dw.run_stage(args, spec)
        info, report = dw.replay_one(self.world.tmp / "s")
        self.assertEqual(info["mode"], "smoke")
        path = self.world.tmp / "s/downstream.json"
        forged = a.load(path)
        forged["prebuilt"]["logroot"] = "0" * 64
        path.write_text(json.dumps(forged))
        with self.assertRaises(dw.Refusal):
            dw.replay_one(self.world.tmp / "s")

    def test_replay_checks_a_selftests_stored_output_against_its_digest(self):
        args, spec = self.world.info("s", "smoke", names=["arith-selftest"])
        report = dw.run_stage(args, spec)
        entry = report["runs"][0]
        path = self.world.tmp / "s" / entry["receipt"]
        receipt = json.loads(gzip.decompress(path.read_bytes()))
        receipt["stdout"] += "more\n"
        path.write_bytes(gzip.compress(dw.dumps(receipt).encode(), mtime=0))
        report["runs"][0]["seal"] = a.seal(path)
        (self.world.tmp / "s/downstream.json").write_text(dw.dumps(report))
        with self.assertRaisesRegex(dw.Refusal, "stored output"):
            dw.replay_one(self.world.tmp / "s")


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


class Sealed(unittest.TestCase):
    def test_the_code_is_sealed_with_the_snapshots_and_dat_modules(self):
        for name in ("task32_snapshots.py", "task32_dat.py",
                     "startup_gate.py", "task32_cases.py",
                     "task32_downstream.py", "loading.py"):
            self.assertIn(name, dw.CODE)
        self.assertEqual(sorted(dw.code_seals()), sorted(dw.CODE))

    def test_the_history_is_empty_until_a_record_exists(self):
        self.assertEqual(dw.HISTORY, {})

    def test_a_record_carries_the_current_seal_or_one_the_history_lists(self):
        now = dw.code_seals()
        dw.check_code(now)
        old = dict(now, **{"task32_dat.py": dict(bytes=1, sha256="0" * 64)})
        with self.assertRaisesRegex(dw.Refusal, "task32_dat.py.*HISTORY"):
            dw.check_code(old)
        with mock.patch.object(dw, "HISTORY", {
                "task32_dat.py": [old["task32_dat.py"]]}):
            dw.check_code(old)
        with self.assertRaises(dw.Refusal):
            dw.check_code({k: v for k, v in now.items()
                           if k != "loading.py"})


class Cli(unittest.TestCase):
    def parse(self, *argv):
        return dw.build_parser().parse_args(list(argv))

    def common(self):
        return ["--repo", "r", "--base-root", "b", "--cand-root", "c",
                "--manifest", "m"]

    def test_run_commands_take_no_ledger(self):
        for command in ("smoke", "pilot", "run", "extend", "followup"):
            extra = ["--first", "f"] if command == "extend" else []
            argv = [command, *self.common(), "--output", "o", *extra]
            self.parse(*argv)
            with self.assertRaises(SystemExit), \
                    mock.patch("sys.stderr"):
                self.parse(*argv, "--ledger", "x")

    def test_read_only_commands_take_a_ledger(self):
        self.parse("replay", "x", "--ledger", "l")
        self.parse("dispose", "--stage", "x", "--out", "o", "--ledger", "l")
        self.parse("predeclare", *self.common(), "--out", "o", "--ledger",
                   "l", "--control", "c")

    def test_control_needs_a_pilot_and_recover_a_repository(self):
        with self.assertRaises(SystemExit), mock.patch("sys.stderr"):
            self.parse("control", *self.common(), "--output", "o")
        self.parse("control", *self.common(), "--output", "o", "--pilot",
                   "p")
        self.parse("recover", "--repo", "r")

    def test_the_pilot_is_ten_pairs_and_r_has_a_cap(self):
        self.assertEqual(dw.PILOT_PAIRS, 10)
        self.assertGreaterEqual(dw.R_CAP, 1)


class Chain(Base):
    """smoke -> pilot -> control -> counts -> first stage -> second stage ->
    follow-up -> disposition, on fake processes. logroot is noisy in the
    first stage (a control outside the window: the second stage) and
    borderline in the second (a valid control, inconclusive: follow-up);
    rat has a valid control and is borderline already in the first stage
    (a follow-up without a second stage); everything else passes."""

    def commit_counts(self, path):
        w = self.world
        git(w.repo, "add", os.path.relpath(path, w.repo))
        git(w.repo, "commit", "-q", "-m", "counts " + path.name)

    def test_the_whole_chain(self):
        w = self.world
        ledger = w.ledger()
        perf = w.repo / "src/simp/tests/performance"
        args, spec = w.info("smoke", "smoke")
        smoke = dw.run_stage(args, spec)
        self.assertTrue(smoke["success"], smoke.get("failure"))
        self.assertEqual(len(smoke["runs"]), 30)
        self.assertTrue(smoke["outcome"]["probe"]["ok"])
        self.assertTrue(smoke["outcome"]["probe"]["complete"])
        self.assertEqual(smoke["outcome"]["probe"]["heaps"],
                         list(cases.HEAPS))
        args, spec = w.info("pilot", "pilot")
        pilot_run = dw.run_stage(args, spec)
        self.assertTrue(pilot_run["success"], pilot_run.get("failure"))
        self.assertEqual(len(pilot_run["runs"]), 300)
        self.assertTrue(pilot_run["outcome"]["covered"])
        self.assertEqual({p["reps"] for p in
                          pilot_run["outcome"]["pilot"].values()}, {1})
        self.assertEqual({c[1] for c in w.calls[30:]}, {"base"})
        args, spec = w.info("control", "control", pilot=w.tmp / "pilot")
        control = dw.run_stage(args, spec)
        self.assertTrue(control["success"], control.get("failure"))
        self.assertTrue(control["outcome"]["negative_control"]["detected"])
        # predeclare: replays the three, writes the counts
        pargs = w.args("x", pilot=w.tmp / "pilot", smoke=w.tmp / "smoke",
                       control=w.tmp / "control")
        # snapshots rebuilt since the information runs: another manifest
        text = w.manifest.read_text()
        w.manifest.write_text(json.dumps(json.loads(text), indent=1))
        with self.assertRaisesRegex(dw.Refusal, "other snapshots"):
            dw.predeclare_first(pargs)
        with self.assertRaisesRegex(dw.Refusal, "--pilot was made on "
                                    "other snapshots"):
            dw.info_spec(w.args("c", pilot=w.tmp / "pilot"), "control")
        w.manifest.write_text(text)
        counts = dw.predeclare_first(pargs)
        self.assertEqual(set(counts["reps"]), set(cases.NAMES))
        self.assertEqual(counts["r_cap"], dw.R_CAP)
        self.assertTrue(counts["control"]["detected"])
        self.assertGreater(counts["time_estimate_seconds"]["total"], 0)
        self.assertIn("scan_seconds", counts["smoke"]["overheads"])
        self.assertEqual(sorted(counts["smoke"]["overheads"][
            "verify_seconds"]), ["after", "before"])
        estimate = counts["time_estimate_seconds"]
        self.assertGreater(estimate["scan_seconds"], 0)
        self.assertGreater(estimate["verify_seconds"], 0)
        self.assertAlmostEqual(
            estimate["total"], sum(estimate["per_unit"].values()) +
            estimate["verify_seconds"])
        counts_path = perf / "counts.json"
        counts_path.write_text(dw.dumps(counts))
        with self.assertRaisesRegex(dw.Refusal, "not committed"):
            dw.first_spec(w.args("a", counts=counts_path))
        self.commit_counts(counts_path)
        # a snapshot rebuilt after predeclare: another manifest seal
        text = w.manifest.read_text()
        w.manifest.write_text(json.dumps(json.loads(text), indent=1))
        with self.assertRaisesRegex(dw.Refusal, "rebuilt"):
            dw.first_spec(w.args("a", counts=counts_path))
        w.manifest.write_text(text)
        # an information run needs its `info` line and a successful
        # `info-end` with its seal in the ledger
        empty = w.tmp / "other-ledger.jsonl"
        tg_append = dw.tg.ledger_append
        tg_append(empty, event="info", table=dw.TABLE, attempt="x",
                  mode="smoke", key="k", seed="s", output="o",
                  checkout="c")
        with self.assertRaisesRegex(dw.Refusal, "no `info` line"):
            dw.info_run(w.tmp / "smoke", dw.gate_key(dw.pins_of(
                w.args("z"))[0]), "smoke", empty, mseal=dw.pins_of(
                    w.args("z"))[1])
        lines = ledger.read_text().splitlines(keepends=True)
        short = w.tmp / "short-ledger.jsonl"
        self.assertIn('"info-end"', lines[-1])  # the control's
        short.write_text("".join(lines[:-1]))
        with self.assertRaisesRegex(dw.Refusal, "no successful `info-end`"):
            dw.info_run(w.tmp / "control", dw.gate_key(dw.pins_of(
                w.args("z"))[0]), "control", short, [cases.CONTROL_UNIT],
                mseal=dw.pins_of(w.args("z"))[1])
        # first stage
        for name in cases.NAMES:
            w.profile[name] = (1.0, 0.001)
        w.profile["logroot"] = (1.0, 0.06)
        w.profile["rat"] = (1.03, 0.003)
        spec = dw.first_spec(w.args("first", counts=counts_path))
        first = dw.run_stage(w.args("first", counts=counts_path), spec)
        self.assertTrue(first["success"], first.get("failure"))
        self.assertEqual(len(first["runs"]), 15 * 20 * 4)
        res = first["outcome"]["results"]
        self.assertEqual(
            sorted(n for n in cases.NAMES if res[n]["decision"] != "pass"),
            ["logroot", "rat"])
        self.assertFalse(res["logroot"]["control_valid"])
        self.assertEqual(res["rat"]["decision"], "inconclusive")
        self.assertTrue(res["rat"]["control_valid"])
        self.assertEqual(dw.exit_of(first), 2)
        with self.assertRaisesRegex(dw.Refusal, "judged attempt"):
            w.run("first-again", spec, counts=counts_path)
        chain = dw.replay_chain(w.tmp / "first", ledger,
                                counts=counts_path, repo=w.repo)
        self.assertEqual([e["stage"] for e in chain], ["first"])
        disp = dw.disposition(chain, ledger)
        self.assertEqual(disp["workloads"]["logroot"]["note"],
                         dw.NOTE_SECOND)
        self.assertEqual(disp["workloads"]["rat"]["status"], "followup")
        # a follow-up is refused while a workload is owed its second stage
        with self.assertRaisesRegex(dw.Refusal, "second stage"):
            dw.followup_plan(chain)
        # second stage: only the control-limited logroot, the grid's pairs
        w.profile["logroot"] = (1.03, 0.01)
        sargs = w.args("second", first=w.tmp / "first", counts=counts_path)
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
        self.assertEqual([e["stage"] for e in chain], ["first", "second"])
        disp = dw.disposition(chain, ledger)
        self.assertEqual(disp["workloads"]["logroot"]["status"],
                         "followup")
        self.assertEqual(disp["counts"]["followup"], 2)
        with self.assertRaises(dw.Refusal):  # at most one second stage
            w.run("second-again", spec2)
        # follow-up: pairs from the first stage's control, own seed and
        # counts, committed alone first
        fargs = w.args("fu", stage=w.tmp / "second", followup=True,
                       counts=counts_path)
        fcounts = dw.predeclare_followup(fargs)
        self.assertEqual(sorted(fcounts["workloads"]),
                         ["logroot", "rat"])
        for name in fcounts["workloads"]:
            self.assertEqual(fcounts["pairs"][name],
                             res[name]["second_stage_pairs"])
            self.assertGreaterEqual(fcounts["pairs"][name], 40)
            self.assertLessEqual(fcounts["pairs"][name], 120)
        self.assertNotEqual(fcounts["seed"], dw.EXTENSION_SEED)
        self.assertEqual(fcounts["seed"], dw.FOLLOWUP_SEED)
        fpath = perf / "followup.json"
        fpath.write_text(dw.dumps(fcounts))
        fa = w.args("followup", followup_counts=fpath, counts=counts_path)
        with self.assertRaisesRegex(dw.Refusal, "not committed"):
            dw.followup_spec(fa)
        self.commit_counts(fpath)
        w.profile["logroot"] = (1.0, 0.01)
        w.profile["rat"] = (1.0, 0.001)
        fspec = dw.followup_spec(fa)
        follow = dw.run_stage(fa, fspec)
        self.assertTrue(follow["success"], follow.get("failure"))
        for name in ("logroot", "rat"):
            self.assertEqual(follow["outcome"]["results"][name][
                "decision"], "pass")
        self.assertEqual(dw.exit_of(follow), 0)
        chain = dw.replay_chain(w.tmp / "followup", ledger,
                                counts=counts_path,
                                followup_counts=fpath, repo=w.repo)
        self.assertEqual([e["stage"] for e in chain],
                         ["first", "second", "followup"])
        self.assertEqual(dw.dumps(chain[-1]["report"]), dw.dumps(follow))
        disp = dw.disposition(chain, ledger)
        self.assertEqual(disp["status"], "pass")
        self.assertEqual(disp["counts"]["pass"], 15)
        self.assertEqual(len(disp["attempts"]), 3)
        self.assertFalse(any(r["void"] for r in disp["attempts"]))
        self.assertEqual([r["mode"] for r in disp["info_runs"]],
                         ["smoke", "pilot", "control"])
        self.assertEqual({r["status"] for r in disp["info_runs"]},
                         {"success"})
        self.assertEqual(disp["redraws"], [])
        self.assertTrue(all(r["checkout"] == str(w.repo)
                            for r in disp["attempts"] + disp["info_runs"]))
        with self.assertRaises(dw.Refusal):  # the follow-up is one draw
            w.run("followup-again", fspec, counts=counts_path)
        # the entry points reach the same results
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
        sides, _ = dw.pins_of(w.args("z"))
        with mock.patch.object(dw, "code_seals",
                               lambda: dict(counts["code"], x="y")):
            with self.assertRaisesRegex(dw.Refusal, "code changed"):
                dw.load_counts(counts_path, sides, "first", w.repo)
        # a counts file of another gate, or over the R cap, is refused
        other = dict(sides, cand=dict(sides["cand"], pin="2" * 40))
        with self.assertRaisesRegex(dw.Refusal, "another gate"):
            dw.load_counts(counts_path, other, "first", w.repo)

    def test_predeclare_refuses_without_a_detected_control_or_over_the_cap(
            self):
        w = self.world
        names = ["logroot"]
        for mode in ("smoke", "pilot"):
            args, spec = w.info(mode, mode, names=names)
            self.assertTrue(dw.run_stage(args, spec)["success"])
        args, spec = w.info("control", "control", pilot=w.tmp / "pilot")
        w.ignore_busy = True
        self.assertTrue(dw.run_stage(args, spec)["success"])
        pargs = w.args("x", pilot=w.tmp / "pilot", smoke=w.tmp / "smoke",
                       control=w.tmp / "control")
        # not all workloads: refused before anything else
        with self.assertRaisesRegex(dw.Refusal, "workloads the counts"):
            dw.predeclare_first(pargs)

    def test_redraws_list_void_attempts_and_failed_information_runs(self):
        w = self.world
        w.fault = lambda u, s, n: "exit"
        args, spec = w.info("s", "smoke", names=["logroot"])
        self.assertFalse(dw.run_stage(args, spec)["success"])
        self.assertFalse(w.run("v", w.spec(["logroot"]))["success"])
        state, found = dw.read_ledger(w.ledger())
        attempts = dw.attempts_table(found, dw.reasons(found))
        infos = dw.info_runs(state)
        self.assertEqual([r["status"] for r in infos], ["failed"])
        self.assertTrue(attempts[0]["void"])
        redrawn = dw.redraws(attempts, infos)
        self.assertEqual(sorted(r["kind"] for r in redrawn),
                         ["decision first", "smoke"])


class HeapAnchorParsing(unittest.TestCase):
    def test_assignments_replace_or_append(self):
        with tempfile.TemporaryDirectory() as tmp:
            folder = Path(tmp, "src/h")
            folder.mkdir(parents=True)
            (folder / "Holmakefile").write_text(
                "A_DEPS = one two \\\n  three\n"
                "A_DEPS += four ../x/five $(skip)\n"
                "B_DEPS := six\n"
                "B_DEPS := seven\n"
                "C_DEPS +=eight\n"
                "DEPS = nope\nOTHER = nope2\n")
            self.assertEqual(
                dw.heap_anchors(tmp, "src/h/heap"),
                {"one", "two", "three", "four", "five", "seven", "eight"})
            self.assertIsNone(dw.heap_anchors(tmp, "bin/hol.state"))


class CasesAgreeWithS1(unittest.TestCase):
    """Every unit of task32_cases is something S1's snapshots require, so a
    sequence or verify that stops short cannot leave a unit unbuilt."""

    def test_every_unit_has_a_required_product(self):
        required = set(snap.REQUIRED_PRODUCTS)
        for unit in cases.UNITS:
            if unit["kind"] == "theory":
                entry = ("theory", unit["dir"], unit["theory"])
            else:
                # the build's own log of the selftest, as S1 names it
                logs = [n for k, d, n in required
                        if k == "log" and d == unit["dir"]]
                self.assertEqual(len(logs), 1, unit["name"])
                entry = ("log", unit["dir"], logs[0])
                self.assertTrue(
                    logs[0] == unit["name"] + ".log" or
                    logs[0].endswith("selftest.log") or
                    logs[0].endswith("selftest2.log"), unit["name"])
            self.assertIn(entry, required, unit["name"])
        heaps = {u["heap"] for u in cases.UNITS if u["heap"] not in (
            "bin/hol.state0", "bin/hol.state", cases.NUMHEAP)}
        self.assertEqual(heaps, {cases.REALHEAP})
        self.assertIn(("file", *cases.REALHEAP.rsplit("/", 1)), required)
        # no required unit directory is left out of the cases
        dirs = {u["dir"] for u in cases.UNITS}
        for kind, directory, name in required:
            if kind != "file":
                self.assertIn(directory, dirs, name)

    def test_the_heap_parents_are_heaps_of_the_cases(self):
        for heap, parent in cases.HEAP_PARENTS.items():
            self.assertIn(heap, cases.HEAPS)
            self.assertTrue(parent in cases.HEAPS or
                            parent == "bin/hol.state0")


class CandidateCheck(unittest.TestCase):
    """check_candidate on a real git repository."""

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory(prefix="t32-cand-")
        self.addCleanup(self.dir.cleanup)
        self.repo = Path(self.dir.name)
        git(self.repo, "init", "-q")
        for rel in ("src/boss/tests/t.sml", "src/boss/compiled.sml",
                    "src/simp/tests/performance/p.py"):
            (self.repo / rel).parent.mkdir(parents=True, exist_ok=True)
            (self.repo / rel).write_text("0\n")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "c31")
        self.c31 = git(self.repo, "rev-parse", "HEAD")
        patcher = mock.patch.object(dw, "COMPILED_REF", self.c31)
        patcher.start()
        self.addCleanup(patcher.stop)

    def commit(self, rel):
        path = self.repo / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("changed\n")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", rel)
        return git(self.repo, "rev-parse", "HEAD")

    def sides(self, cand):
        return dict(base=dict(pin=a.BASE), cand=dict(pin=cand))

    def test_changes_under_any_tests_directory_pass(self):
        self.commit("src/boss/tests/t.sml")
        self.commit("src/simp/tests/performance/p.py")
        cand = self.commit("src/boss/tests/tracked-defaults/new.sml")
        self.assertEqual(dw.check_candidate(self.repo, self.sides(cand)),
                         self.c31)

    def test_a_compiled_change_is_refused(self):
        cand = self.commit("src/boss/compiled.sml")
        with self.assertRaisesRegex(dw.Refusal, "compiled sources differ"):
            dw.check_candidate(self.repo, self.sides(cand))

    def test_the_baseline_must_be_the_pin(self):
        with self.assertRaises(dw.Refusal):
            dw.check_candidate(self.repo, dict(
                base=dict(pin="2" * 40), cand=dict(pin=self.c31)))


class MissingUnits(Base):
    def test_a_snapshot_without_a_unit_names_the_unit_and_the_path(self):
        root = self.world.roots["base"]
        unit = cases.BY_NAME["rat"]
        ctx = dict(roots=self.world.roots)
        shutil.rmtree(root / unit["dir"] / ".hol")
        with self.assertRaisesRegex(
                dw.Refusal, r"theory product missing: \.sig \(base side, "
                r"unit rat: expected .*/%s/\.hol/objs/ratTheory\."
                r"\{sig,dat,sml\}\)" % unit["dir"]):
            dw.originals(ctx, ["rat"])
        test = cases.BY_NAME["reduce-selftest"]
        (root / test["dir"] / "selftest.exe").unlink()
        with self.assertRaisesRegex(
                dw.Refusal, r"selftest.exe missing: base side, unit "
                r"reduce-selftest: expected .*selftest\.exe"):
            dw.originals(ctx, ["reduce-selftest"])


class CountsDefaults(unittest.TestCase):
    def test_a_run_that_used_counts_is_not_replayed_without_them(self):
        with tempfile.TemporaryDirectory() as tmp:
            absent = Path(tmp, "no.json")
            report = dict(stage="first", counts=dict(seal=None))
            with mock.patch.object(dw, "COUNTS", absent):
                with self.assertRaisesRegex(dw.Refusal, "is absent"):
                    dw.counts_file_for(report, None, None)
                present = Path(tmp, "yes.json")
                present.write_text("{}")
                self.assertEqual(dw.counts_file_for(report, present, None),
                                 present)
            with mock.patch.object(dw, "FOLLOWUP_COUNTS", absent):
                with self.assertRaisesRegex(dw.Refusal, "--followup-counts"):
                    dw.counts_file_for(dict(report, stage="followup"),
                                       None, None)
            self.assertIsNone(dw.counts_file_for(
                dict(stage="first", counts=None), None, None))
            self.assertIsNone(dw.counts_file_for(
                dict(report, stage="second"), None, None))


class HelpRenders(unittest.TestCase):
    def help_of(self, argv):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            with self.assertRaises(SystemExit) as ctx:
                dw.build_parser().parse_args(argv)
        self.assertEqual(ctx.exception.code, 0, argv)
        self.assertIn("usage", out.getvalue(), argv)
        return " ".join(out.getvalue().split())

    def test_every_help_renders(self):
        self.help_of(["--help"])
        for name in dw.COMMANDS:
            flat = self.help_of([name, "--help"])
            if name == "control":
                self.assertIn("is %.0f%% of its median" % (100 * dw.BUSY),
                              flat)

    def test_commands_match_parser(self):
        # No public API lists the subparsers; the top-level usage line
        # names every choice, so read it from there.
        flat = self.help_of(["--help"])
        usage = flat[flat.index("{"):flat.index("}")]
        self.assertEqual(set(usage.strip("{").split(",")),
                         set(dw.COMMANDS))


if __name__ == "__main__":
    unittest.main()

