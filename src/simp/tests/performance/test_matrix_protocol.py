"""Cross-component matrix selection, storage and serialization contracts."""
import copy
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "compatibility"))
import acceptance as a
import performance_schema as ps
import run_paired as rp


class MatrixProtocolTests(unittest.TestCase):
    def test_fixture_installation(self):
        for fixture in ("MatrixPerformance.sml", "ClientPerformance.sml"):
            with tempfile.TemporaryDirectory() as tmp:
                dst = Path(tmp)
                rp.install_fixtures(dst, performance=True,
                                    matrix_fixture=fixture)
                self.assertEqual((dst / "Performance.sml").read_bytes(),
                                 (HERE / fixture).read_bytes())
                self.assertEqual((dst / "MatrixSupport.sml").exists(),
                                 fixture == "MatrixPerformance.sml")

    def test_suite_rejects_invalid_parameters(self):
        good = dict(suite="matrix", case="frag_create", size=10000)
        self.assertEqual(ps.suite_options(good),
                         dict(labels=("frag_create",),
                              consumed={"frag_create": 1}, storage=False))
        for mutation in (dict(case="unknown"), dict(size=3),
                         dict(size=True), dict(case="traversal_construct")):
            with self.assertRaises(ValueError):
                ps.suite_options(dict(good, **mutation))

    def test_graph_parser_fails_closed(self):
        line = "@@MATRIX_STORAGE\tstorage_graph\t10,20,30,80,40,90,50,60,70,10,40"
        row, = ps.graphs([line], "storage_graph", 10)
        self.assertEqual(row["compiled_increment"], 50)
        for lines, case, size in (([], "storage_graph", 10),
                ([line, line], "storage_graph", 10),
                ([line], "frag_create", 10), ([line], "storage_graph", 1),
                ([line.replace(",50,", ",51,")], "storage_graph", 10),
                ([line[:-2] + "41"], "storage_graph", 10),
                ([line.replace("10,20", "10,~20")], "storage_graph", 10),
                (["prefix" + line], "storage_graph", 10)):
            with self.subTest(lines=lines, case=case, size=size):
                with self.assertRaises(ValueError):
                    ps.graphs(lines, case, size)

    def test_retained_scaling_keeps_each_interval_and_zero(self):
        rows = []
        for size in a.SIZES:
            metrics = {}
            for metric in ("compiled_increment_words",
                           "fragment_increment_words"):
                metrics[metric] = a.paired_statistics([
                    dict(baseline=10 + size * 4, candidate=10 + size * 4)
                    for _ in range(10)])
            value = dict(case="storage_graph", size=size, metrics=metrics)
            rows.append(dict(control=copy.deepcopy(value), candidate=value))
        report = a.retained_scaling(rows)
        self.assertEqual(report["status"], "measured")
        self.assertEqual(len(report["adjacent_intervals"]), 20)
        self.assertTrue(all(r["words_per_rule"]["decision"] == "pass"
                            for r in report["adjacent_intervals"]))
        for row in rows[-1]["candidate"]["metrics"][
                "compiled_increment_words"]["observations"]:
            row["candidate"] += 1
        report = a.retained_scaling(rows)
        failures = [r for r in report["adjacent_intervals"]
                    if r["words_per_rule"]["decision"] == "fail"]
        self.assertEqual(len(failures), 1)
        self.assertEqual(failures[0]["upper"], 10000)
        self.assertEqual(a.retained_scaling(rows[:-1])["status"], "blocked")
        self.assertIsNone(a.retained_scaling([]))

    def test_reentrant_inherited_locks(self):
        # A throwaway repository: the real checkout's lock may be held
        # by a real benchmark and must not be written by a unit test.
        temp = tempfile.TemporaryDirectory(prefix="matrix-lock-")
        self.addCleanup(temp.cleanup)
        repo = Path(temp.name) / "repo"
        repo.mkdir()
        subprocess.run(["git", "init", "-q", str(repo)], check=True,
                       stdin=subprocess.DEVNULL)
        with a.serial_lock(repo) as fds:
            env = dict(os.environ,
                       HOL4_PERF_LOCK_FDS=",".join(map(str, fds)))
            command = [sys.executable, "-B", "-c",
                       "import sys; sys.path.insert(0,sys.argv[1]); "
                       "from acceptance import serial_lock; "
                       "lock=serial_lock(sys.argv[2]); lock.__enter__(); "
                       "print('inherited lock verified')", str(HERE), str(repo)]
            result = subprocess.run(command, env=env, pass_fds=fds,
                                    text=True, capture_output=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("inherited lock verified", result.stdout)
            env.pop("HOL4_PERF_LOCK_FDS")
            result = subprocess.run(command, env=env, text=True,
                                    capture_output=True, timeout=10)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("lock busy", result.stderr)


if __name__ == "__main__":
    unittest.main()
