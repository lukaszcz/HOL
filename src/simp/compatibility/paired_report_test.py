#!/usr/bin/env python3
"""Negative controls for evidence comparison (no HOL products needed)."""

import json
from pathlib import Path
import tempfile
import unittest

from paired_report import compare


class EvidenceComparison(unittest.TestCase):
    def fixture(self, directory, fresh=False):
        lanes = {}
        for lane in ("reference", "branch"):
            observations = ["OBS callback=first", "OBS callback=second",
                            "OBS exception=none", "OBS warnings=0"]
            record = {"run_exit": 0, "build_exit": 0,
                      "observations": observations}
            if fresh:
                record.update(precondition_clean=True,
                              expected_load_path=f"/private/{lane}/simpLib")
                observations.append("OBS load.path=" +
                                    record["expected_load_path"])
            lanes[lane] = {"scenarios" if fresh else "suites":
                           {"control": record}}
            (directory / f"{lane}-control.run.log").write_text(
                "\n".join(observations) + "\n")
        manifest = {"passed": True, "lanes": lanes, "commands": []}
        self.save(directory, manifest)
        return manifest

    def save(self, directory, manifest):
        (directory / "manifest.json").write_text(json.dumps(manifest))

    def test_equal_and_lane_paths(self):
        for fresh in (False, True):
            with tempfile.TemporaryDirectory() as work:
                path = Path(work)
                self.fixture(path, fresh)
                result, _ = compare(path, fresh)
                self.assertEqual(result["inputs"][0]["observed"], "equal")

    def test_order_warning_exception_and_missing_observations(self):
        for replacement in (["OBS callback=second", "OBS callback=first",
                             "OBS exception=none", "OBS warnings=0"],
                            ["OBS callback=first", "OBS callback=second",
                             "OBS exception=Interrupt", "OBS warnings=0"],
                            ["OBS callback=first", "OBS callback=second",
                             "OBS exception=none", "OBS warnings=1"], []):
            with tempfile.TemporaryDirectory() as work:
                path = Path(work)
                manifest = self.fixture(path)
                manifest["lanes"]["branch"]["suites"]["control"][
                    "observations"] = replacement
                self.save(path, manifest)
                with self.assertRaises(ValueError):
                    compare(path, False)

    def test_raw_diagnostic_not_discarded(self):
        with tempfile.TemporaryDirectory() as work:
            path = Path(work)
            self.fixture(path)
            with (path / "branch-control.run.log").open("a") as stream:
                stream.write("warning: unexpected diagnostic\n")
            with self.assertRaises(ValueError):
                compare(path, False)

    def test_manifest_log_disagreement(self):
        with tempfile.TemporaryDirectory() as work:
            path = Path(work)
            manifest = self.fixture(path)
            for lane in ("reference", "branch"):
                manifest["lanes"][lane]["suites"]["control"][
                    "observations"][0] = "OBS callback=fabricated"
            self.save(path, manifest)
            with self.assertRaises(ValueError):
                compare(path, False)

    def test_terminal_newline_difference(self):
        with tempfile.TemporaryDirectory() as work:
            path = Path(work)
            self.fixture(path)
            log = path / "branch-control.run.log"
            log.write_bytes(log.read_bytes().rstrip(b"\n"))
            with self.assertRaises(ValueError):
                compare(path, False)

    def test_wrong_load_path_and_unclean_launcher(self):
        for key, value in (("expected_load_path", "/wrong/path"),
                           ("precondition_clean", False)):
            with tempfile.TemporaryDirectory() as work:
                path = Path(work)
                manifest = self.fixture(path, True)
                manifest["lanes"]["branch"]["scenarios"]["control"][key] = value
                self.save(path, manifest)
                with self.assertRaises(ValueError):
                    compare(path, True)


if __name__ == "__main__":
    unittest.main()
