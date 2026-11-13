"""task37_builds.py (D7): command construction, the receipt and the
attribution join on synthetic logs. No build runs here: a fake runner
stands in for the processes."""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import task37_builds as b


def git(repo, *argv):
    return subprocess.run(
        ["git", "-C", str(repo), "-c", "user.name=t", "-c",
         "user.email=t@t", *argv], stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, check=True).stdout.decode().strip()


class Repo(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)
        self.repo = self.dir / "main"
        self.repo.mkdir()
        git(self.repo, "init", "-q")
        (self.repo / "f").write_text("1\n")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "one")
        self.base = git(self.repo, "rev-parse", "HEAD")
        (self.repo / "f").write_text("2\n")
        git(self.repo, "commit", "-q", "-a", "-m", "two")
        self.cand = git(self.repo, "rev-parse", "HEAD")


def log_text(dirs, start=(13, "Nov", 0, 0, 0)):
    """A build log: `Building directory D [13 Nov, hh:mm:ss]` lines (with
    the ANSI bold of bin/build) at the given offsets in seconds."""
    day, mon, h, m, s = start
    lines = ["Cleaning out sigobj"]
    for d, off in dirs:
        t = h * 3600 + m * 60 + s + off
        dd = day + t // 86400
        t %= 86400
        lines.append("\x1b[1mBuilding directory %s [%d %s, %02d:%02d:%02d]"
                     "\x1b[0m" % (d, dd, mon, t // 3600, t % 3600 // 60,
                                  t % 60))
        lines.append("Holmake output")
    return "\n".join(lines) + "\n"


class Commands(unittest.TestCase):
    def test_the_two_builds_and_their_pairs(self):
        self.assertEqual(b.build_argv("routine"), [
            "bin/build", "-t", "--seq=tools/sequences/upto-parallel"])
        self.assertEqual(b.build_argv("full"), ["bin/build", "-t", "-F"])
        self.assertEqual(b.KINDS["routine"]["pairs"], 3)
        self.assertEqual(b.KINDS["full"]["pairs"], 2)
        with self.assertRaises(b.Refusal):
            b.build_argv("quick")

    def test_pairs_alternate_ab_ba(self):
        self.assertEqual([b.pair_order(i) for i in range(3)], [
            ("base", "cand"), ("cand", "base"), ("base", "cand")])

    def test_each_side_is_a_fresh_shared_clone_configured_by_poly(self):
        steps = b.step_commands("/main", "/dev/shm/x/t", "a" * 40, "full")
        names = [s[0] for s in steps]
        self.assertEqual(names, ["clone", "checkout", "configure", "build"])
        self.assertEqual(steps[0][1][:4], ["git", "clone", "--shared",
                                           "--no-checkout"])
        self.assertEqual(steps[0][1][-2:], ["/main", "/dev/shm/x/t"])
        self.assertIn("--detach", steps[1][1])
        self.assertEqual(steps[1][1][-1], "a" * 40)
        self.assertEqual(steps[2][1], ["poly"])
        self.assertEqual(steps[2][3], "/dev/shm/x/t/tools/smart-configure.sml")
        self.assertEqual(steps[3][1], ["bin/build", "-t", "-F"])
        self.assertEqual(steps[3][2], "/dev/shm/x/t")

    def test_the_plan_takes_pair_overrides(self):
        self.assertEqual([(e["kind"], e["pairs"]) for e in b.plan(
            ["routine", "full"])], [("routine", 3), ("full", 2)])
        self.assertEqual(b.plan(["full"], {"full": 1})[0]["pairs"], 1)
        with self.assertRaises(b.Refusal):
            b.plan(["full"], {"full": 0})
        self.assertEqual(b.parse_pairs(["full=1"]), {"full": 1})
        with self.assertRaises(b.Refusal):
            b.parse_pairs(["slow=1"])

    def test_default_signals_reach_a_child_that_inherited_ignored_ones(self):
        code = ("import signal,sys;"
                "print([signal.getsignal(signal.SIGINT) != signal.SIG_IGN] + "
                "[signal.getsignal(s) == signal.SIG_DFL for s in "
                "(signal.SIGHUP, signal.SIGTERM)])")
        ignoring = ("import signal,sys;"
                    "signal.signal(signal.SIGINT, signal.SIG_IGN);"
                    "signal.signal(signal.SIGHUP, signal.SIG_IGN);"
                    "from importlib import util;"
                    "spec = util.spec_from_file_location('b', %r);"
                    "m = util.module_from_spec(spec);"
                    "spec.loader.exec_module(m);"
                    "import subprocess;"
                    "print(subprocess.run([sys.executable, '-c', %r], "
                    "preexec_fn=m.restore_default_signals, "
                    "stdout=subprocess.PIPE, "
                    "stdin=subprocess.DEVNULL).stdout.decode())" % (
                        str(HERE / "task37_builds.py"), code))
        done = subprocess.run([sys.executable, "-B", "-c", ignoring],
                              stdin=subprocess.DEVNULL,
                              stdout=subprocess.PIPE, check=True)
        self.assertEqual(done.stdout.decode().strip(),
                         "[True, True, True]")

    def test_the_real_runner_records_exit_wall_cpu_and_a_new_session(self):
        with tempfile.TemporaryDirectory() as tmp:
            log = Path(tmp) / "x.log"
            step = b.real_runner(
                [sys.executable, "-c",
                 "import os;print(os.getsid(0)==os.getpid());"
                 "sum(range(10**6));raise SystemExit(3)"],
                tmp, dict(os.environ), str(log))
            self.assertEqual(step["exit"], 3)
            self.assertGreater(step["user_s"] + step["sys_s"], 0)
            self.assertGreater(step["wall_s"], 0)
            self.assertEqual(log.read_text().strip(), "True")
            self.assertEqual(len(step["load_start"]), 3)
            self.assertFalse(step["timed_out"])

    def test_the_real_runner_counts_the_cpu_of_a_grandchild(self):
        burn = "x = 0\nfor i in range(6 * 10 ** 6): x += i"
        child = ("import subprocess, sys; "
                 "subprocess.run([sys.executable, '-c', %r], check=True)"
                 % burn)
        with tempfile.TemporaryDirectory() as tmp:
            step = b.real_runner([sys.executable, "-c", child], tmp,
                                 dict(os.environ), str(Path(tmp) / "x.log"))
            alone = b.real_runner([sys.executable, "-c", burn], tmp,
                                  dict(os.environ),
                                  str(Path(tmp) / "y.log"))
        self.assertEqual(step["exit"], 0)
        # the grandchild's burn is in the child's rusage (it waited), and
        # so in the step's: about the same CPU as running it directly
        self.assertGreater(step["user_s"] + step["sys_s"],
                           0.8 * (alone["user_s"] + alone["sys_s"]))

    def test_the_real_runner_kills_a_step_that_exceeds_its_timeout(self):
        with tempfile.TemporaryDirectory() as tmp:
            step = b.real_runner(
                ["sh", "-c", "sleep 60 & sleep 60"], tmp, dict(os.environ),
                str(Path(tmp) / "x.log"), timeout=0.5)
        self.assertTrue(step["timed_out"])
        self.assertNotEqual(step["exit"], 0)
        self.assertLess(step["wall_s"], 20)


class Limits(unittest.TestCase):
    def test_shm_room(self):
        self.assertEqual(b.check_room(20, 8, 5 * b.GB), 5 * b.GB)
        with self.assertRaisesRegex(b.Refusal, "exceeds"):
            b.check_room(20, 8, 13 * b.GB)


class Waiting(unittest.TestCase):
    def test_a_build_waits_for_room_then_starts(self):
        used = iter([19 * b.GB, 18 * b.GB, 6 * b.GB])
        slept = []
        got, waited = b.await_room(20, 5, 600, 60, sleep=slept.append,
                                   used=lambda: next(used))
        self.assertEqual((got, waited, slept), (6 * b.GB, 120, [60, 60]))

    def test_a_build_that_never_gets_room_is_refused(self):
        with self.assertRaisesRegex(b.Refusal, "limit"):
            b.await_room(20, 5, 120, 60, sleep=lambda s: None,
                         used=lambda: 19 * b.GB)


class Run(Repo):
    def fake(self, log=None, fail=None, seen=None):
        """A runner that makes the tree on `clone` and writes a build log
        with `Building directory` lines; costs differ by side."""
        def runner(argv, cwd, env, logfile, stdin=None, timeout=None):
            if seen is not None:
                seen.append((argv, cwd, stdin))
            if argv[:2] == ["git", "clone"]:
                Path(argv[-1]).mkdir(parents=True)
                Path(argv[-1], "marker").write_text("x")
            if argv[0] == "bin/build":
                side = "cand" if "cand" in Path(cwd).name else "base"
                extra = 5 if side == "cand" else 0
                dirs = [("src/a", 0), ("src/b", 10 + extra)]
                if side == "cand":
                    dirs.append(("src/ext", 20))
                Path(logfile).write_text(log or log_text(dirs))
            else:
                Path(logfile).write_text("")
            code = 1 if fail and argv[0] == fail else 0
            return dict(exit=code, wall_s=40.0, user_s=30.0, sys_s=5.0,
                        start_utc="2026-11-13T00:00:00Z",
                        end_utc="2026-11-13T00:00:40Z",
                        load_start=[1.0, 2.0, 3.0],
                        load_end=[1.5, 2.0, 3.0])
        return runner

    def run_all(self, **kw):
        kw.setdefault("runner", self.fake())
        return b.run_all(self.repo, self.base, self.cand, self.dir / "shm",
                         self.dir / "out", **kw)

    def test_a_run_records_every_build_and_deletes_the_trees(self):
        r = self.run_all(kinds=["routine", "full"], pairs={"routine": 3,
                                                           "full": 2})
        self.assertTrue(r["complete"])
        self.assertEqual(b.validate_receipt(r), [])
        self.assertEqual(len(r["runs"]), 10)
        orders = [(x["kind"], x["pair"], x["label"]) for x in r["runs"]]
        self.assertEqual(orders[:4], [
            ("routine", 0, "base"), ("routine", 0, "cand"),
            ("routine", 1, "cand"), ("routine", 1, "base")])
        self.assertTrue(all(x["deleted"] for x in r["runs"]))
        self.assertFalse((self.dir / "shm").exists())
        saved = json.loads((self.dir / "out/receipt.json").read_text())
        self.assertEqual(saved, json.loads(json.dumps(r)))
        run = r["runs"][0]
        self.assertEqual([s["name"] for s in run["steps"]],
                         ["clone", "checkout", "configure", "build"])
        for key in ("exit", "wall_s", "user_s", "sys_s", "load_start",
                    "load_end", "log"):
            self.assertIn(key, run["build"])
        self.assertEqual(r["pins"]["base"], self.base)
        self.assertEqual(r["pins"]["cand"], self.cand)
        self.assertIn("nice", r["host"])
        self.assertTrue((self.dir / "out" / run["build"]["log"]).is_file())

    def test_only_one_tree_is_on_disk_at_a_time(self):
        present = []

        def probe(argv, cwd, env, logfile, stdin=None, timeout=None):
            if argv[0] == "bin/build":
                present.append(sorted(p.name for p in
                                      (self.dir / "shm").iterdir()
                                      if p.name != "tmp"))
            return self.fake()(argv, cwd, env, logfile, stdin, timeout)
        self.run_all(kinds=["routine"], pairs={"routine": 2}, runner=probe)
        self.assertEqual(present, [
            ["routine-p0-base"], ["routine-p0-cand"],
            ["routine-p1-cand"], ["routine-p1-base"]])

    def test_a_failed_build_is_recorded_not_fatal(self):
        r = self.run_all(kinds=["full"], pairs={"full": 1},
                         runner=self.fake(fail="bin/build"))
        self.assertEqual([x["build"]["exit"] for x in r["runs"]], [1, 1])
        self.assertTrue(r["complete"])

    def test_the_build_gets_the_timeout_and_the_setup_steps_theirs(self):
        seen = []

        def runner(argv, cwd, env, logfile, stdin=None, timeout=None):
            seen.append((argv[0], timeout))
            return self.fake()(argv, cwd, env, logfile, stdin, timeout)
        self.run_all(kinds=["routine"], pairs={"routine": 1}, runner=runner,
                     limits=dict(shm_gb=20, reserve_gb=5, timeout_s=77))
        self.assertEqual([t for a_, t in seen if a_ == "bin/build"],
                         [77, 77])
        self.assertEqual({t for a_, t in seen if a_ != "bin/build"},
                         {b.SETUP_TIMEOUT_S})

    def test_failed_builds_are_listed_and_give_a_distinct_status(self):
        failing = self.fake(fail="bin/build")
        r = self.run_all(kinds=["full"], pairs={"full": 1}, runner=failing)
        self.assertEqual([x[3] for x in b.failed_builds(r)],
                         ["exit 1", "exit 1"])
        argv = ["run", "--repo", str(self.repo), "--base", self.base,
                "--cand", self.cand, "--root", str(self.dir / "shm2"),
                "--out", str(self.dir / "out2"), "--kinds", "full",
                "--pairs", "full=1"]
        real = b.run_all
        sink = self.dir / "sink"
        with open(sink, "w") as stream, mock.patch.object(
                b, "run_all", lambda *a_, **k: real(
                    *a_, **dict(k, runner=failing))), \
                mock.patch.object(sys, "stderr", stream):
            self.assertEqual(b.main(argv), b.FAILED_BUILDS)
        self.assertIn("FAILED builds", sink.read_text())

    def test_a_failed_configure_stops_that_side_without_a_build(self):
        r = self.run_all(kinds=["full"], pairs={"full": 1},
                         runner=self.fake(fail="poly"))
        self.assertTrue(all(x["build"] is None for x in r["runs"]))
        self.assertTrue(r["complete"])
        self.assertEqual([[s["name"] for s in x["steps"]]
                          for x in r["runs"]][0][-1], "configure")

    def test_an_interrupt_deletes_the_tree_and_keeps_the_receipt(self):
        count = []

        def runner(argv, cwd, env, logfile, stdin=None, timeout=None):
            count.append(argv[0])
            if argv[0] == "bin/build":
                raise KeyboardInterrupt("signal 15")
            return self.fake()(argv, cwd, env, logfile, stdin, timeout)
        with self.assertRaises(KeyboardInterrupt):
            self.run_all(kinds=["routine"], runner=runner)
        saved = json.loads((self.dir / "out/receipt.json").read_text())
        self.assertFalse(saved["complete"])
        self.assertFalse(any((self.dir / "shm").glob("routine-*")))

    def test_refusals(self):
        (self.dir / "shm").mkdir()
        (self.dir / "shm" / "stray").write_text("x")
        with self.assertRaisesRegex(b.Refusal, "not empty"):
            self.run_all()
        (self.dir / "shm" / "stray").unlink()
        with self.assertRaisesRegex(b.Refusal, "cannot resolve"):
            b.run_all(self.repo, "f" * 40, self.cand, self.dir / "shm",
                      self.dir / "out", runner=self.fake())
        with mock.patch.object(b, "shm_used", return_value=19 * b.GB):
            with self.assertRaisesRegex(b.Refusal, "limit"):
                self.run_all(limits=dict(shm_gb=20, reserve_gb=5,
                                         wait_s=0))

    def test_a_shared_clone_is_not_a_source(self):
        clone = self.dir / "clone"
        git(self.dir, "clone", "-q", "--shared", str(self.repo), str(clone))
        with self.assertRaisesRegex(b.Refusal, "borrows"):
            b.check_repo(clone, dict(base=self.base, cand=self.cand))
        repo, full, head = b.check_repo(self.repo, dict(
            base=self.base[:10], cand=self.cand))
        self.assertEqual(full["base"], self.base)
        self.assertEqual(head, self.cand)

    def test_dry_run_builds_nothing(self):
        out = self.dir / "dry.out"
        with open(out, "w") as stream, mock.patch.object(
                sys, "stdout", stream):
            code = b.main(["run", "--repo", str(self.repo), "--base",
                           self.base, "--cand", self.cand, "--root",
                           str(self.dir / "shm"), "--out",
                           str(self.dir / "o"), "--dry-run"])
        self.assertEqual(code, 0)
        text = out.read_text()
        self.assertEqual(text.count("bin/build -t -F"), 4)
        self.assertEqual(text.count("--seq=tools/sequences/upto-parallel"),
                         6)
        self.assertFalse((self.dir / "shm").exists())


class Attribution(Repo):
    def test_building_times_strip_ansi_and_handle_midnight(self):
        text = log_text([("a", 0), ("b", 30), ("c", 100)],
                        start=(13, "Nov", 23, 59, 40))
        self.assertEqual(b.building_times(text), [("a", 0), ("b", 30),
                                                  ("c", 100)])
        self.assertEqual(b.building_times("no lines\n"), [])

    def test_durations_run_to_the_next_line_and_the_end(self):
        times = [("a", 0), ("b", 30), ("a", 50)]
        self.assertEqual(b.durations(times, 90), {"a": 30 + 40, "b": 20})

    def synthetic(self, name="o"):
        base = log_text([("src/a", 0), ("src/b", 10), ("src/c", 40)])
        cand = log_text([("src/a", 0), ("src/b", 18), ("src/ext", 28),
                         ("src/c", 60)])
        out = self.dir / name
        (out / "logs").mkdir(parents=True)
        runs = []
        for i, (label, text, wall) in enumerate(
                [("base", base, 50), ("cand", cand, 75),
                 ("cand", cand.replace("[13 Nov", "[14 Nov"), 75),
                 ("base", base, 50)]):
            log = "logs/routine-p%d-%s.log" % (i // 2, label)
            (out / log).write_text(text)
            runs.append(dict(
                kind="routine", pair=i // 2, order="AB", label=label,
                pin="a" * 40, steps=[], tree_kb=1, deleted=True,
                build=dict(exit=0, wall_s=wall, user_s=1, sys_s=1,
                           load_start=[0, 0, 0], load_end=[0, 0, 0],
                           log=log)))
        # pair 1 is BA: the order of the labels in the list
        runs[2]["pair"], runs[3]["pair"] = 1, 1
        return dict(schema=b.SCHEMA, host={}, pins=dict(
            base="b" * 40, cand="c" * 40, repo="r", repo_head="h"),
            limits={}, plan=[dict(kind="routine", pairs=2, argv=[])],
            runs=runs, complete=True), out

    def test_the_join_reports_deltas_and_candidate_only_directories(self):
        receipt, out = self.synthetic()
        self.assertEqual(b.validate_receipt(receipt), [])
        data = b.attribute(receipt, lambda p: (out / p).read_text())
        k = data["kinds"]["routine"]
        by = {r["directory"]: r for r in k["common"]}
        self.assertEqual(by["src/b"]["base_s"], 30)
        self.assertEqual(by["src/b"]["cand_s"], 10 + 0)  # 18 -> 28
        self.assertEqual(by["src/b"]["delta_s"], -20)
        self.assertEqual(by["src/c"]["base_s"], 10)
        self.assertEqual(by["src/c"]["cand_s"], 15)
        self.assertEqual(k["only_cand"], [dict(directory="src/ext",
                                               seconds=32)])
        self.assertEqual(k["only_base"], [])
        self.assertEqual(k["wall_s"], dict(base=50, cand=75))
        self.assertEqual(k["common"][0]["directory"], "src/b")  # by |delta|
        self.assertEqual(k["only_cand_total_s"], 32)

    def test_a_failed_build_is_excluded_from_the_medians(self):
        receipt, out = self.synthetic()
        receipt["runs"][2]["build"]["exit"] = 1      # a cand build
        # its (shifted) log would change src/b's median: it is not read
        (out / receipt["runs"][2]["build"]["log"]).write_text(
            log_text([("src/a", 0), ("src/b", 500)]))
        data = b.attribute(receipt, lambda p: (out / p).read_text())
        k = data["kinds"]["routine"]
        self.assertEqual(k["runs"], dict(base=2, cand=1))
        self.assertEqual(k["failed"], [dict(pair=1, label="cand",
                                            why="exit 1")])
        self.assertEqual(data["failed"][0]["kind"], "routine")
        self.assertEqual(k["wall_s"]["cand"], 75)
        by = {r["directory"]: r for r in k["common"]}
        self.assertEqual(by["src/b"]["cand_s"], 10)
        receipt["runs"][2]["build"]["exit"] = 0
        receipt["runs"][3]["build"]["timed_out"] = True
        data = b.attribute(receipt, lambda p: (out / p).read_text())
        self.assertEqual(data["kinds"]["routine"]["failed"][0]["why"],
                         "timed out")

    def test_attribute_cli_reports_failed_builds_with_status_5(self):
        receipt, out = self.synthetic()
        receipt["runs"][0]["build"]["exit"] = 2
        (out / "receipt.json").write_text(json.dumps(receipt))
        sink = self.dir / "sink"
        with open(sink, "w") as stream, mock.patch.object(
                sys, "stdout", stream):
            self.assertEqual(b.main([
                "attribute", str(out / "receipt.json"), "--out",
                str(self.dir / "a.json")]), b.FAILED_BUILDS)
        self.assertIn("FAILED build", sink.read_text())

    def test_attribute_cli_writes_the_json_and_a_summary(self):
        receipt, out = self.synthetic()
        (out / "receipt.json").write_text(json.dumps(receipt))
        target = self.dir / "attr.json"
        sink = self.dir / "sink"
        with open(sink, "w") as stream, mock.patch.object(
                sys, "stdout", stream):
            self.assertEqual(b.main(["attribute", str(out / "receipt.json"),
                                     "--out", str(target)]), 0)
        self.assertIn("cand-only src/ext", sink.read_text())
        self.assertIn("routine", json.loads(target.read_text())["kinds"])
        self.assertEqual(b.main(["attribute", str(out / "receipt.json"),
                                 "--out", str(target)]), 3)

    def test_a_malformed_receipt_is_refused(self):
        receipt, out = self.synthetic()
        del receipt["runs"][0]["build"]["wall_s"]
        with self.assertRaisesRegex(b.Refusal, "wall_s"):
            b.attribute(receipt, lambda p: "")
        receipt, _ = self.synthetic("o2")
        receipt["runs"].pop()
        self.assertTrue(any("pair" in p for p in
                            b.validate_receipt(receipt)))
        self.assertEqual(b.validate_receipt(dict(schema="x")),
                         ["schema is not " + b.SCHEMA])


if __name__ == "__main__":
    unittest.main()
