#!/usr/bin/env python3
"""Fail-closed controls for the isolated consumer driver (no HOL stubs)."""
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest

DRIVER = Path(__file__).with_name("run_task25_consumer.py")
spec = importlib.util.spec_from_file_location("task25", DRIVER)
task25 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(task25)


class Controls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="task25-control-")
        self.root = Path(self.temp.name)
        self.runner = task25.Runner(self.root, self.root, self.root,
                                    self.root, self.root, self.root)

    def tearDown(self):
        self.temp.cleanup()

    def run_command(self, body, **kwargs):
        return self.runner.run("control", [sys.executable, "-c", body], **kwargs)

    def test_failed_process_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "command failed"):
            self.run_command("print('OK'); raise SystemExit(1)")
        self.assertEqual(self.runner.manifest["runs"][0]["exit"], 1)

    def test_zero_exit_static_error_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "static/runtime error"):
            self.run_command("print('error in load fixture : Static Errors')")

    def test_missing_observation_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "missing marker"):
            self.run_command("print('not a test')", marker="TASK25_DONE")

    def test_success_observed(self):
        self.run_command("print('TASK25_DONE')", marker="TASK25_DONE")
        self.assertEqual(self.runner.manifest["runs"][0]["exit"], 0)

    def test_negative_test_labels_not_static_errors(self):
        self.run_command("print('failed unification restores state ... OK')",
                         marker="OK")

    def test_source_drift_rejected(self):
        source = self.root / "source.sml"
        source.write_text("original")
        expected = task25.inventory(self.root)
        source.write_text("changed")
        with self.assertRaisesRegex(RuntimeError, "source drift"):
            task25.verify(self.root, expected)

    def test_missing_source_rejected(self):
        with self.assertRaises(FileNotFoundError):
            task25.verify(self.root, {"missing.sml": {"sha256": "none"}})

    def test_nonstandard_launcher_rejected(self):
        launcher = self.root / "selftest.exe"
        launcher.write_text("#!/bin/sh\nexit 0\n")
        with self.assertRaisesRegex(RuntimeError, "nonstandard launcher"):
            self.runner.launcher(launcher, "selftest")


if __name__ == "__main__":
    unittest.main(verbosity=2)
