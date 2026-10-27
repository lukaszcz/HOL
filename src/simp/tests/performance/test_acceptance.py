#!/usr/bin/env python3
"""TASK28 protocol, statistics, real controls and build-admission regressions.

Synthetic build receipts below test admission only. They are not HOL builds.
"""
import argparse
import copy
import gzip
import json
import math
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

sys.dont_write_bytecode = True
import acceptance as a


def stamped_command(command, stdout, cwd="/archive/repo"):
    data = stdout.encode()
    return dict(command=command, cwd=cwd, exit=0, timed_out=False,
                stdout=stdout, stdout_sha256=a.hashlib.sha256(data).hexdigest(),
                stdout_bytes=len(data))


def checked_git(root, *args):
    subprocess.run(["git", "-C", str(root), *args], check=True,
                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def repository(root):
    root.mkdir()
    checked_git(root, "init", "-q")
    checked_git(root, "config", "user.name", "TASK28 test")
    checked_git(root, "config", "user.email", "task28@example.invalid")
    for name, text in ((".gitignore", "bin/\nsigobj/\nholproject.toml\n"),
                       ("tracked", "source\n"),
                       ("tools/smart-configure.sml", "(* fixture *)\n")):
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    checked_git(root, "add", ".")
    checked_git(root, "commit", "-qm", "synthetic admission fixture")
    return a.git(root, "rev-parse", "HEAD")


class StatisticsTests(unittest.TestCase):
    def rows(self, ratios):
        return [{"baseline": 1, "candidate": r} for r in ratios]

    def test_strict_boundaries_no_budgets(self):
        for low, high, expected in ((1, 1, "pass"), (0.9, 1, "pass"),
                                    (1 + 1e-12, 1.1, "fail"),
                                    (1, 1.1, "inconclusive"),
                                    (0.9, 1.1, "inconclusive")):
            self.assertEqual(a.decision(low, high), expected)

    def test_deterministic_bootstrap_and_raw_pairs(self):
        rows = self.rows([0.5, 0.9, 1, 1, 1, 1, 1, 1.1, 1.2, 1.5])
        first = a.paired_statistics(rows)
        self.assertEqual(first, a.paired_statistics(rows))
        self.assertEqual(first["observations"], rows)
        self.assertEqual(first["paired_ratios"], [r["candidate"] for r in rows])
        self.assertEqual(first["median_paired_ratio"], 1)
        self.assertEqual(first["decision"], "inconclusive")

    def test_reproducible_slowdown_any_size_fails(self):
        for ratio in (1.000001, 1.1, 2):
            report = a.paired_statistics(self.rows([ratio] * 10))
            self.assertEqual(report["decision"], "fail")
            self.assertEqual(report["paired_ratio_bootstrap_95_percent"],
                             [ratio, ratio])

    def test_equal_and_faster_pass(self):
        for ratio in (0, 0.9, 1):
            self.assertEqual(a.paired_statistics(self.rows([ratio] * 10))[
                "decision"], "pass")

    def test_zero_gc_is_not_dropped_or_called_pass(self):
        for candidate in (0, 1):
            rows = [{"baseline": 0, "candidate": candidate}] + self.rows([1] * 9)
            data = a.paired_statistics(rows)
            self.assertEqual(data["decision"], "inconclusive")
            self.assertIsNone(data["paired_ratio_bootstrap_95_percent"])
            self.assertEqual(len(data["paired_ratios"]), 10)
            self.assertIsNone(data["paired_ratios"][0])

    def test_at_least_ten_pairs(self):
        for n in (0, 1, 9):
            with self.assertRaisesRegex(ValueError, ">=10"):
                a.paired_statistics(self.rows([1] * n))

    def test_invalid_metrics(self):
        for value in (math.nan, math.inf, -1, True, "1", None):
            rows = self.rows([1] * 10)
            rows[3]["candidate"] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                a.paired_statistics(rows)
        rows = self.rows([1] * 10)
        rows[0].pop("candidate")
        with self.assertRaisesRegex(ValueError, "incomplete"):
            a.paired_statistics(rows)

    def test_invalid_intervals(self):
        for low, high in ((-1, 1), (2, 1), (math.nan, 1), (1, math.inf)):
            with self.assertRaises(ValueError):
                a.decision(low, high)

    def test_no_outliers_removed(self):
        rows = self.rows([1] * 9 + [1000000])
        data = a.paired_statistics(rows)
        self.assertEqual(len(data["paired_ratios"]), 10)
        self.assertEqual(data["paired_ratios"][-1], 1000000)
        self.assertEqual(a.POLICY["outliers"], "none removed")
        self.assertIsNone(a.POLICY["budgets"])


class ControlTests(unittest.TestCase):
    def test_genuine_subprocess_controls(self):
        # No HOL workloads/builds here. Still honor the shared performance lock.
        with a.serial_lock(a.HERE.parents[3]):
            report = a.negative_controls()
        controls = report["controls"]
        for name in ("slowdown", "allocation"):
            self.assertEqual(controls[name]["decision"], "fail")
            self.assertGreater(controls[name][
                "paired_ratio_bootstrap_95_percent"][0], 1)
            self.assertEqual(len(controls[name]["observations"]), 10)
        self.assertEqual(controls["failed"]["rejection"],
                         "failed control process")
        self.assertEqual(controls["missing"]["rejection"],
                         "missing control result")

    def test_failed_process_cannot_pass_with_valid_output(self):
        with self.assertRaisesRegex(ValueError, "failed control process"):
            a.parse_control(subprocess.CompletedProcess([], 7, '{"ok":true}'))

    def test_missing_result_not_a_success_exit(self):
        with self.assertRaisesRegex(ValueError, "missing control result"):
            a.parse_control(subprocess.CompletedProcess([], 0, ""))

    def test_unverified_result_and_bad_metrics(self):
        good = dict(protocol="task28-control-v1", verified=True, consumed=1,
                    cpu=1, wall=1, allocation_bytes=20, peak_bytes=30)
        for key, value in (("verified", False), ("consumed", 0),
                           ("cpu", float("nan")), ("wall", -1)):
            bad = dict(good, **{key: value})
            with self.assertRaises(ValueError):
                a.parse_control(subprocess.CompletedProcess(
                    [], 0, json.dumps(bad)))


class BuildManifestTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="task28-admission-")
        self.addCleanup(self.temp.cleanup)
        self.folder = Path(self.temp.name)
        self.path = self.folder / "manifest.json"
        self.pins, self.roots = {}, {}
        self.poly = self.folder / "poly"
        self.poly.write_text("#!/bin/sh\nprintf 'Poly/ML synthetic TASK28\\n'\n")
        self.poly.chmod(0o755)
        self.doc = dict(schema="task28-independent-build-v1",
                        mode="independent", success=True,
                        runtime_options=["--gcthreads=1"],
                        toolchain={"poly": {
                            "path": str(self.poly),
                            "fingerprint": a.seal(self.poly),
                            "version": "Poly/ML synthetic TASK28"}},
                        selections={})
        for side in ("baseline", "candidate"):
            root = self.folder / side
            pin = repository(root)
            self.pins[side], self.roots[side] = pin, root
            self.assertEqual(a.clean_root(root, pin, pristine=True), root)
            start = time.time_ns()
            products = {}
            for name in ("bin/hol", "bin/Holmake", "bin/hol.state0",
                         "bin/hol.state.min", "bin/build", "holproject.toml",
                         "sigobj/Foo.uo", "sigobj/Foo.ui"):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("fresh synthetic artifact " + side + name)
                # Deterministic synthetic admission times: filesystem write
                # timestamps can be coarser than time.time_ns(). This is not
                # real clean-build evidence.
                os.utime(path, ns=(start + 1, start + 1))
                if name != "bin/build":
                    products[name] = {"path": str(path),
                                      "physical": str(path.resolve()),
                                      "hash": a.seal(path),
                                      "mtime_ns": path.stat().st_mtime_ns}
            steps = []
            for phase in ("configure", "full"):
                log = self.folder / (side + "-" + phase + ".log")
                log.write_text("synthetic admission log; NOT HOL build\n")
                argv = [str(self.poly)] if phase == "configure" else \
                    [str(root / "bin/build"), "-t", "-F"]
                stdin = str(root / "tools/smart-configure.sml") \
                    if phase == "configure" else None
                steps.append(dict(phase=phase, argv=argv, cwd=str(root),
                                  exit=0, timed_out=False, start_ns=start,
                                  end_ns=start, stdin=stdin,
                                  stdin_hash=a.seal(stdin) if stdin else None,
                                  executable_hash=a.seal(argv[0]),
                                  log=str(log), log_hash=a.seal(log)))
            self.doc["selections"][side] = dict(
                root=str(root), pin=pin, fresh_before=True,
                status_before="", ignored_before="", start_ns=start,
                end_ns=time.time_ns(), commands=steps, products=products,
                dependency_inventory=["sigobj/Foo.uo", "sigobj/Foo.ui"])

    def verify(self, document=None):
        self.path.write_text(json.dumps(document or self.doc))
        return a.verify_builds(self.path, self.pins["baseline"],
                               self.pins["candidate"])

    def test_complete_prerequisites_still_block_performance(self):
        report = self.verify()
        self.assertEqual(report["build_prerequisites"], "verified")
        self.assertEqual(report["performance"], "blocked")
        self.assertIn("shared run_paired", report["required_input"])

    def test_missing_every_required_top_field(self):
        for key in self.doc:
            bad = copy.deepcopy(self.doc)
            bad.pop(key)
            with self.subTest(key=key), self.assertRaises((KeyError, ValueError)):
                self.verify(bad)

    def test_wrong_scope_failed_build_and_options(self):
        for key, value in (("mode", "isolated"), ("success", False),
                           ("schema", "unknown"),
                           ("runtime_options", ["--gcthreads=2"])):
            bad = copy.deepcopy(self.doc)
            bad[key] = value
            with self.assertRaises(ValueError):
                self.verify(bad)

    def test_exact_pin_not_alias(self):
        for pin in ("HEAD", self.pins["baseline"][:12], "g" * 40):
            with self.assertRaises(ValueError):
                a.clean_root(self.roots["baseline"], pin)
        bad = copy.deepcopy(self.doc)
        bad["selections"]["baseline"]["pin"] = "0" * 40
        with self.assertRaises(ValueError):
            self.verify(bad)

    def test_changed_live_worktree_pin(self):
        root = self.roots["candidate"]
        (root / "tracked").write_text("changed source\n")
        checked_git(root, "commit", "-qam", "change")
        with self.assertRaisesRegex(ValueError, "pin changed"):
            self.verify()

    def test_dirty_and_untracked_live_worktree(self):
        root = self.roots["candidate"]
        for name in ("tracked", "untracked"):
            path = root / name
            old = path.read_text() if path.exists() else None
            path.write_text("dirty")
            with self.assertRaisesRegex(ValueError, "clean/fresh"):
                self.verify()
            if old is None:
                path.unlink()
            else:
                path.write_text(old)

    def test_pristine_rejects_ignored_builds(self):
        with self.assertRaisesRegex(ValueError, "clean/fresh"):
            a.clean_root(self.roots["baseline"], self.pins["baseline"],
                         pristine=True)

    def test_nonfresh_attestation_and_old_artifacts(self):
        for key, value in (("fresh_before", False), ("status_before", "M foo"),
                           ("ignored_before", "!! cached.uo")):
            bad = copy.deepcopy(self.doc)
            bad["selections"]["baseline"][key] = value
            with self.assertRaises(ValueError):
                self.verify(bad)
        path = self.roots["baseline"] / "bin/hol.state0"
        os.utime(path, ns=(1, 1))
        self.doc["selections"]["baseline"]["products"]["bin/hol.state0"][
            "mtime_ns"] = 1
        with self.assertRaisesRegex(ValueError, "stale"):
            self.verify()

    def test_missing_each_command_field(self):
        for key in self.doc["selections"]["baseline"]["commands"][0]:
            bad = copy.deepcopy(self.doc)
            bad["selections"]["baseline"]["commands"][0].pop(key)
            # stdin_hash is checked for configure, every field is required.
            with self.subTest(key=key), self.assertRaises((KeyError, ValueError)):
                self.verify(bad)

    def test_failed_timed_out_wrong_or_missing_build_command(self):
        for key, value in (("exit", 1), ("timed_out", True),
                           ("argv", ["bin/build"]), ("cwd", "/tmp")):
            bad = copy.deepcopy(self.doc)
            bad["selections"]["candidate"]["commands"][1][key] = value
            with self.assertRaises(ValueError):
                self.verify(bad)
        bad = copy.deepcopy(self.doc)
        bad["selections"]["baseline"]["commands"].pop()
        with self.assertRaises(ValueError):
            self.verify(bad)

    def test_missing_and_changed_logs(self):
        path = Path(self.doc["selections"]["baseline"]["commands"][0]["log"])
        path.write_text("changed log")
        with self.assertRaisesRegex(ValueError, "build log"):
            self.verify()
        path.unlink()
        with self.assertRaisesRegex(ValueError, "build log"):
            self.verify()

    def test_changed_tool_and_executable(self):
        self.doc["toolchain"]["poly"]["fingerprint"]["sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "toolchain"):
            self.verify()
        self.doc["toolchain"]["poly"]["fingerprint"] = a.seal(self.poly)
        path = self.roots["baseline"] / "bin/build"
        path.write_text("changed executable")
        with self.assertRaisesRegex(ValueError, "executable"):
            self.verify()

    def test_wrong_live_runtime_version(self):
        self.doc["toolchain"]["poly"]["version"] = "Poly/ML wrong version"
        with self.assertRaisesRegex(ValueError, "version changed"):
            self.verify()

    def test_changed_configure_input(self):
        path = self.roots["baseline"] / "tools/smart-configure.sml"
        path.write_text("changed")
        # Also rejected as a dirty worktree, before accepting the receipt.
        with self.assertRaises(ValueError):
            self.verify()

    def test_missing_or_changed_heap(self):
        path = self.roots["baseline"] / "bin/hol.state0"
        path.write_text("changed heap")
        with self.assertRaisesRegex(ValueError, "changed build product"):
            self.verify()
        path.unlink()
        with self.assertRaises(OSError):
            self.verify()

    def test_missing_dependency_product_and_inventory(self):
        bad = copy.deepcopy(self.doc)
        bad["selections"]["baseline"]["products"].pop("sigobj/Foo.ui")
        with self.assertRaisesRegex(ValueError, "dependency inventory"):
            self.verify(bad)
        (self.roots["baseline"] / "sigobj/Stale.uo").write_text("old")
        with self.assertRaisesRegex(ValueError, "unrecorded/stale"):
            self.verify()

    def test_shared_roots(self):
        bad = copy.deepcopy(self.doc)
        bad["selections"]["candidate"]["root"] = str(self.roots["baseline"])
        with self.assertRaisesRegex(ValueError, "independent roots"):
            self.verify(bad)

    def test_cross_root_symlink(self):
        path = self.roots["candidate"] / "bin/hol.state0"
        path.unlink()
        path.symlink_to(self.roots["baseline"] / "bin/hol.state0")
        with self.assertRaisesRegex(ValueError, "outside selected root"):
            self.verify()

    def test_internal_dependency_symlinks_allowed(self):
        root = self.roots["candidate"]
        logical = root / "sigobj/Foo.uo"
        physical = root / "bin/Foo.uo"
        logical.rename(physical)
        logical.symlink_to(physical)
        entry = self.doc["selections"]["candidate"]["products"]["sigobj/Foo.uo"]
        entry["physical"] = str(physical)
        self.assertEqual(self.verify()["build_prerequisites"], "verified")

    def test_shared_product_hardlink(self):
        target = self.roots["baseline"] / "bin/hol.state0"
        path = self.roots["candidate"] / "bin/hol.state0"
        path.unlink()
        os.link(target, path)
        entry = self.doc["selections"]["candidate"]["products"]["bin/hol.state0"]
        entry.update(hash=a.seal(path), mtime_ns=path.stat().st_mtime_ns)
        # Meet both intervals exactly at the shared mtime so that the inode
        # guard, rather than the earlier freshness guard, is actually exercised.
        boundary = target.stat().st_mtime_ns
        self.doc["selections"]["baseline"]["end_ns"] = boundary
        selected = self.doc["selections"]["candidate"]
        selected["start_ns"] = boundary
        for step in selected["commands"]:
            step["start_ns"] = step["end_ns"] = boundary
        for selection in self.doc["selections"].values():
            for info in selection["products"].values():
                os.utime(info["path"], ns=(boundary, boundary))
                info["mtime_ns"] = boundary
        with self.assertRaisesRegex(ValueError, "shared independent product"):
            self.verify()

    def test_overlapping_builds(self):
        self.doc["selections"]["candidate"]["start_ns"] = \
            self.doc["selections"]["baseline"]["start_ns"]
        with self.assertRaisesRegex(ValueError, "overlapping"):
            self.verify()


class OrchestrationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="task28-orchestration-")
        self.addCleanup(self.temp.cleanup)
        self.folder = Path(self.temp.name)
        self.root = self.folder / "repo"
        self.pin = repository(self.root)

    def args(self, **changes):
        values = dict(pairs=10, samples=3, batch_seconds=0.2, timeout=20,
                      baseline=self.pin, candidate=self.pin,
                      authorize_measurements=True, output=self.folder / "out",
                      case=["frag_create"], size=[0, 10000], repo=self.root,
                      mode="isolated", build_manifest=None)
        return argparse.Namespace(**dict(values, **changes))

    def test_two_process_lock_excludes_and_releases(self):
        command = [sys.executable, "-B", "-c",
                   "import sys; sys.path.insert(0, sys.argv[1]); "
                   "import acceptance as a; "
                   "with_lock = a.serial_lock(sys.argv[2]); "
                   "with_lock.__enter__()", str(a.HERE), str(self.root)]
        with a.serial_lock(self.root):
            result = subprocess.run(command, stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("lock busy", result.stderr)
        result = subprocess.run(command, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_user_lock_lives_in_agent_files(self):
        lock = self.root / ".agent-files" / (
            "hol4-performance-%d.lock" % os.getuid())
        with a.serial_lock(self.root) as fds:
            self.assertEqual(os.fstat(fds[0]).st_ino, lock.stat().st_ino)
        self.assertTrue(lock.exists(), "lock inode was unlinked")

    def test_lock_stays_held_by_child_after_parent_closes(self):
        with a.serial_lock(self.root) as fds:
            child = subprocess.Popen(
                [sys.executable, "-c", "import sys; sys.stdin.read()"],
                stdin=subprocess.PIPE, pass_fds=fds)
        try:
            with self.assertRaisesRegex(a.Blocked, "lock busy"):
                with a.serial_lock(self.root):
                    self.fail("inherited lock unexpectedly released")
        finally:
            child.communicate(timeout=10)
        with a.serial_lock(self.root):
            pass

    def test_failed_runner_command_log_and_exit_retained(self):
        command = [sys.executable, "-c", "print('executed'); exit(7)"]
        log = self.folder / "failure.log"
        result = a.run_logged(command, log, (), 10)
        self.assertEqual(result["argv"], command)
        self.assertEqual(result["exit"], 7)
        self.assertEqual(result["log_hash"], a.seal(log))
        self.assertIn("executed", log.read_text())

    def test_honors_existing_gitdir_runner_lock(self):
        fd = os.open(self.root / ".git", os.O_RDONLY)
        try:
            a.fcntl.flock(fd, a.fcntl.LOCK_EX | a.fcntl.LOCK_NB)
            with self.assertRaisesRegex(a.Blocked, "lock busy"):
                with a.serial_lock(self.root):
                    self.fail("lock unexpectedly acquired")
        finally:
            os.close(fd)
        with a.serial_lock(self.root):
            pass

    def test_controls_and_candidate_commands_every_case_size(self):
        commands, analyses = [], []

        def execute(command, output, fds, timeout):
            self.assertGreaterEqual(len(fds), 2)
            commands.append(command)
            return {"argv": command, "exit": 0}

        def analyze(folder, **options):
            analyses.append(options)
            return {"metrics": {"cpu": {"decision": "pass"},
                                "wall": {"decision": "pass"},
                                "gc": {"decision": "inconclusive"}}}

        with patch.object(a, "negative_controls", return_value={}), \
                patch.object(a, "run_logged", side_effect=execute), \
                patch.object(a, "analyze", side_effect=analyze):
            report = a.run(self.args(candidate="c" * 40))
        self.assertTrue(report["success"])
        self.assertEqual(len(report["workloads"]), 2)
        self.assertEqual(len(commands), 4)
        self.assertEqual([c[c.index("--candidate") + 1] for c in commands],
                         [self.pin, "c" * 40, self.pin, "c" * 40])
        for command in commands:
            self.assertIn("--matrix-performance", command)
            self.assertEqual(command[command.index("--performance-pairs") + 1],
                             "10")
            self.assertEqual(command[command.index("--performance-case") + 1],
                             "frag_create")
        self.assertEqual([r["size"] for r in analyses], [0, 0, 10000, 10000])

    def test_control_noise_not_subtracted_from_failure(self):
        result = {"metrics": {"cpu": {"decision": "fail"},
                              "wall": {"decision": "pass"}}}
        with patch.object(a, "negative_controls", return_value={}), \
                patch.object(a, "run_logged", return_value={"exit": 0}), \
                patch.object(a, "analyze", side_effect=lambda *x, **k:
                             copy.deepcopy(result)):
            report = a.run(self.args(size=[1000]))
        metrics = report["workloads"][0]["candidate"]["metrics"]
        self.assertEqual(metrics["cpu"]["decision"], "fail")

    def test_baseline_control_failure_invalidates_pass(self):
        results = [{"metrics": {"cpu": {"decision": "fail"}}},
                   {"metrics": {"cpu": {"decision": "pass"}}}]
        with patch.object(a, "negative_controls", return_value={}), \
                patch.object(a, "run_logged", return_value={"exit": 0}), \
                patch.object(a, "analyze", side_effect=results):
            report = a.run(self.args(size=[1000]))
        self.assertEqual(report["workloads"][0]["candidate"]["metrics"][
            "cpu"]["decision"], "inconclusive")

    def test_failure_retains_report_and_does_not_run_next_case(self):
        with patch.object(a, "negative_controls", return_value={}), \
                patch.object(a, "run_logged", side_effect=ValueError("failed")) \
                as launch:
            report = a.run(self.args())
        self.assertFalse(report["success"])
        self.assertEqual(report["failure"], "failed")
        self.assertEqual(launch.call_count, 1)
        self.assertEqual(a.load(self.folder / "out/acceptance.json"), report)

    def test_independent_never_runs_shared_source_runner(self):
        with patch.object(a, "run_logged") as launch:
            report = a.run(self.args(mode="independent"))
        self.assertFalse(report["success"])
        self.assertIn("manifest required", report["blocked"])
        launch.assert_not_called()

    def test_no_overwrite_existing_evidence(self):
        (self.folder / "out").mkdir()
        with self.assertRaises(FileExistsError):
            a.run(self.args())

    def test_options_rejected_before_work(self):
        for options in ({"pairs": 9}, {"samples": 2}, {"batch_seconds": 0.01},
                        {"authorize_measurements": False}, {"timeout": 0},
                        {"size": [9]}, {"size": [1, 1]},
                        {"case": ["../escape"]}, {"case": ["x", "x"]},
                        {"candidate": "HEAD"}):
            with self.subTest(options=options), self.assertRaises(ValueError):
                a.run(self.args(**options))
        self.assertFalse((self.folder / "out").exists())

    def test_safe_evidence_paths(self):
        path = self.folder / "evidence"
        path.mkdir()
        (self.folder / "outside").write_text("outside")
        (path / "link").symlink_to(self.folder / "outside")
        for name in ("../outside", str(self.folder / "outside"), "link", ""):
            with self.assertRaises(ValueError):
                a.safe_child(path, name)


class ArchivedAcceptanceTests(unittest.TestCase):
    """Construct complete archived protocol, not precomputed summary ratios."""
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="task28-archive-")
        self.addCleanup(self.temp.cleanup)
        self.folder = Path(self.temp.name)
        self.pin = "a" * 40
        self.options = dict(case="frag_create", size=1000, baseline=self.pin,
                            candidate=self.pin, pairs=10, samples=3,
                            seconds=0.2)
        self.hash = {"sha256": "b" * 64, "bytes": 5}
        self.manifest = dict(success=True, repo="/archive/repo",
            performance=dict(pairs=10, samples=3, batch_seconds=0.2,
                             suite="matrix", case="frag_create", size=1000,
                             outliers="none removed"),
            runtime_options=["--gcthreads=1", "run",
                             "--holstate=/archive/repo/bin/hol.state0"],
            tools={name: copy.deepcopy(self.hash) for name in
                   ("bin/hol", "bin/hol.state0", "bin/hol.state.min",
                    "bin/Holmake", "holproject.toml", "/tools/poly",
                    "/tools/libpolyml.so")},
            poly_version=stamped_command(["/tools/poly", "--version"],
                                        "Poly/ML 5.9.2 Release\n"),
            dynamic_libraries=stamped_command(
                ["ldd", "/archive/repo/bin/hol"],
                "libpolyml.so => /tools/libpolyml.so (0x123)\n"),
            inputs={"src/simp/tests/performance/MatrixPerformance.sml": self.hash,
                    "src/simp/tests/performance/MatrixSupport.sml": self.hash,
                    "src/simp/tests/performance/RuntimeMetrics.sml": self.hash}, selections={}, runs=[])
        self.receipts = {}
        for side in ("baseline", "candidate"):
            private = "/archive/" + side
            launcher = ("#!/bin/sh\nset -e\n/archive/repo/bin/hol "
                        "--gcthreads=1 run "
                        "--holstate=/archive/repo/bin/hol.state0 runner\n"
                        "exit 0\n")
            selected = dict(private=private, revision=self.pin,
                            build_exit=0, launcher=launcher,
                            fixture_products={"Performance.sml": self.hash,
                                              "MatrixSupport.sml": self.hash,
                                              "RuntimeMetrics.sml": self.hash},
                            products={"paired.exe": {
                                "sha256": a.hashlib.sha256(
                                    launcher.encode()).hexdigest(),
                                "bytes": len(launcher.encode())}}, sources=[])
            for name in ("Traverse", "simpLib"):
                selected["sources"].append(dict(
                    git_path="src/simp/src/" + name + ".sml",
                    private_path=private + "/" + name + ".sml", **self.hash))
            self.manifest["selections"][side] = selected
        for pair in range(10):
            order = ("candidate", "baseline") if pair % 2 else \
                ("baseline", "candidate")
            for side in order:
                private = "/archive/" + side
                heap = "/archive/repo/src/portableML/prelude.sml"
                sources = [private + "/" + n + ".sml" for n in
                           ("Traverse", "simpLib", "MatrixSupport",
                            "RuntimeMetrics", "Performance")]
                events = [["begin", side, "performance", "none"],
                          ["cwd", private],
                          ["holdir", "/archive/repo", "/archive/repo"],
                          ["preloaded", "HolKernel"], ["heapfile", heap],
                          ["search", private],
                          ["search", "/archive/repo/sigobj"]]
                for path in sources[:-1]:
                    events += [["use", path], ["used", path]]
                events += [["use", sources[-1]],
                    ["observation", "timer.accounting",
                     "0.25,0.2,0.01,0.02,0.005,0.22,0.015,0.02,5"],
                    ["check", "timer accounting", "pass"],
                    ["check", "workload inputs", "pass"],
                    ["observation", "calibration.frag_create",
                     "1,0.25,0.2,0.01,0.02,0.005,0.22,0.015,0.02,1"]]
                for sample in range(3):
                    events += [["observation", "batch.frag_create",
                        str(sample) +
                        ",1,0.25,0.2,0.01,0.02,0.005,0.22,0.015,0.02,1"],
                        ["check", "results frag_create", "pass"]]
                events += [["observation", "sink", "9"],
                           ["used", sources[-1]]]
                events += [["loaded", p] for p in [heap, *sources]]
                events += [["end", "pass", "5"]]
                import performance_schema
                observations, data = performance_schema.validate(
                    events, 3, 0.2, labels=("frag_create",),
                    consumed={"frag_create": 1}, storage=False)
                paths = {p: dict(physical=p, related_products={}, **self.hash)
                         for p in [heap, *sources]}
                receipt = dict(accepted=True, exit=0, timed_out=False,
                    fixture="performance", control="none", selection=side,
                    pair=pair, cwd=private, command=[private + "/paired.exe"],
                    environment=dict(PAIR_SELECTION=side, PAIR_PRIVATE=private,
                        PAIR_FIXTURE="performance", PAIR_TARGET="Performance",
                        PAIR_CONTROL="none", PERF_SAMPLES="3",
                        PERF_SECONDS="0.2", PERF_CASE="frag_create",
                        PERF_SIZE="1000"),
                    result=dict(events=events, observations=observations,
                        expected_test_count=5, outcome="pass", paths=paths),
                    measurements=data, diagnostics=[], storage_graph=[])
                import runtime_metrics as rm
                snapshot = {k: 0 for k in (*rm.COUNTERS, *rm.HEAP)}
                snapshot.update(rssBytes=1024, hwmBytes=2048)
                receipt["diagnostics"] = ["@@MATRIX_RUNTIME\t" + json.dumps(
                    dict(schema=1, stage=stage, iterations=1,
                         before=snapshot, after=snapshot))
                    for stage in ("calibration", "sample", "sample", "sample")]
                receipt["runtime"] = rm.validate(receipt["diagnostics"], data)
                name = "%02d-%s.json.gz" % (pair, side)
                self.receipts[name] = receipt
                self.manifest["runs"].append(dict(receipt=name, accepted=True,
                                                   exit=0))
        shared = "/archive/repo/src/portableML/prelude.sml"
        self.manifest["shared_inputs"] = {shared: copy.deepcopy(
            self.first()["result"]["paths"][shared])}
        self.persist()

    def persist(self):
        (self.folder / "manifest.json").write_text(json.dumps(self.manifest))
        for name, value in self.receipts.items():
            (self.folder / name).write_bytes(gzip.compress(
                json.dumps(value).encode(), mtime=0))

    def analyze(self):
        return a.analyze(self.folder, **self.options)

    def first(self):
        return self.receipts[self.manifest["runs"][0]["receipt"]]

    def test_complete_archive_passes_per_metric(self):
        report = self.analyze()
        self.assertEqual(report["mode"], "isolated")
        self.assertIn("NOT independent", report["scope"])
        self.assertEqual(set(report["metrics"]), {"cpu", "wall", "gc"})
        self.assertTrue(all(m["decision"] == "pass"
                            for m in report["metrics"].values()))

    def test_missing_and_reordered_pair(self):
        runs = self.manifest["runs"]
        self.manifest["runs"] = runs[:-1]
        self.persist()
        with self.assertRaisesRegex(ValueError, "fresh-process pair"):
            self.analyze()
        self.manifest["runs"] = list(reversed(runs))
        self.persist()
        with self.assertRaisesRegex(ValueError, "fresh-process pair"):
            self.analyze()

    def test_duplicate_receipt(self):
        self.manifest["runs"][1] = self.manifest["runs"][0]
        self.persist()
        with self.assertRaisesRegex(ValueError, "duplicate receipt"):
            self.analyze()

    def test_failed_process_and_missing_results(self):
        record = self.first()
        record["exit"] = 7
        self.persist()
        with self.assertRaisesRegex(ValueError, "failed or negative"):
            self.analyze()
        record["exit"] = 0
        record["result"]["events"].pop(-1)
        self.persist()
        with self.assertRaises(ValueError):
            self.analyze()

    def test_every_event_required(self):
        record = self.first()
        original = copy.deepcopy(record["result"]["events"])
        for index in range(len(original)):
            record["result"]["events"] = original[:index] + original[index + 1:]
            self.persist()
            with self.subTest(index=index), self.assertRaises(
                    (ValueError, KeyError, IndexError)):
                self.analyze()

    def test_altered_measurements_rejected(self):
        self.first()["measurements"]["sink"] += 1
        self.persist()
        with self.assertRaisesRegex(ValueError, "inconsistent archived result"):
            self.analyze()

    def test_wrong_case_size_options_and_revision(self):
        for key, value in (("case", "other"), ("size", 10),
                           ("pairs", 9), ("samples", 4),
                           ("batch_seconds", 0.4), ("outliers", "trimmed")):
            old = self.manifest["performance"][key]
            self.manifest["performance"][key] = value
            self.persist()
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.analyze()
            self.manifest["performance"][key] = old
        self.manifest["selections"]["candidate"]["revision"] = "c" * 40
        self.persist()
        with self.assertRaisesRegex(ValueError, "revision"):
            self.analyze()

    def test_wrong_process_environment(self):
        record = self.first()
        for key, value in (("PERF_CASE", "other"), ("PERF_SIZE", "0"),
                           ("PERF_SAMPLES", "4"), ("PAIR_TARGET", "Other")):
            old = record["environment"][key]
            record["environment"][key] = value
            self.persist()
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.analyze()
            record["environment"][key] = old

    def test_mutated_fixture_binding_and_selected_source(self):
        self.first()["result"]["paths"]["/archive/baseline/Traverse.sml"][
            "sha256"] = "0" * 64
        self.persist()
        with self.assertRaisesRegex(ValueError, "source/hash"):
            self.analyze()
        self.first()["result"]["paths"]["/archive/baseline/Traverse.sml"][
            "sha256"] = self.hash["sha256"]
        self.manifest["inputs"][
            "src/simp/tests/performance/MatrixPerformance.sml"] = {}
        self.persist()
        with self.assertRaisesRegex(ValueError, "matrix fixture binding"):
            self.analyze()

    def test_wrong_search_preloaded_and_loaded_paths(self):
        record = self.first()
        original = copy.deepcopy(record["result"]["events"])
        for index, replacement in ((3, ["preloaded", "simpLib"]),
                                   (5, ["search", "/wrong/root"]),
                                   (-2, ["loaded", "/wrong/Performance.sml"])):
            record["result"]["events"] = copy.deepcopy(original)
            record["result"]["events"][index] = replacement
            self.persist()
            with self.assertRaises(ValueError):
                self.analyze()


if __name__ == "__main__":
    unittest.main()
