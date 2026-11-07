#!/usr/bin/env python3
"""TASK31 gate 1 analysis (task31_identity.py) on synthetic closures and
work rows, and the snapshot wrapper (task31_snapshot.py) on a toy tree."""
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import task31_identity as idt
import task31_snapshot as snap

REPO = "/repo"


def fake(side, source="s1", product="p1", extra=None, order=None):
    """(manifest, receipt, snapshot) of one side: a private source with a
    product, and a shared one."""
    private = "/tmp/simp-paired-x/" + side
    manifest = dict(repo=REPO, selections={side: dict(
        private=private, sources=[], shared_dependencies=dict(products={}))})
    paths = {
        "%s/A.sml" % private: dict(
            physical="%s/A.sml" % private, sha256=source, bytes=3,
            related_products={"%s/A.uo" % private: dict(
                sha256="raw-" + side, bytes=2)}),
        REPO + "/src/B.sml": dict(
            physical=REPO + "/src/B.sml", sha256="b", bytes=1,
            related_products={})}
    use = order or ["%s/A.sml" % private, REPO + "/src/B.sml"]
    events = [["use", p] for p in use]
    events.append(["heapfile", REPO + "/src/H.sml"])
    if extra:
        paths.update(extra)
    files = {"A.sml": [3, source, source], "A.uo": [2, "raw-" + side,
                                                    product]}
    return (manifest, dict(result=dict(events=events, paths=paths)),
            {side: dict(root=private, files=files)})


class Closure(unittest.TestCase):
    def closures(self, **tweak):
        out = {}
        for side in idt.SIDES:
            manifest, receipt, snapshot = fake(
                side, **(tweak if side == "candidate" else {}))
            out[side] = idt.closure(manifest, receipt, snapshot, side)
        return out

    def test_the_private_directory_of_a_side_is_not_a_difference(self):
        found = self.closures()
        self.assertEqual(idt.compare(found["baseline"],
                                     found["candidate"]), [])
        self.assertEqual(sorted(found["baseline"]["entries"]),
                         ["private/A.sml", "shared/src/B.sml"])
        self.assertEqual(found["baseline"]["order"],
                         ["<private>/A.sml", "<repo>/src/B.sml"])
        self.assertEqual(found["baseline"]["heap"], ["<repo>/src/H.sml"])

    def test_a_source_a_product_an_order_a_missing_file_differ(self):
        for tweak, kind in (
                (dict(source="s2"), "source"), (dict(product="p2"),
                                                 "product"),
                (dict(order=["/repo/src/B.sml",
                             "/tmp/simp-paired-x/candidate/A.sml"]),
                 "order")):
            found = self.closures(**tweak)
            kinds = {d["kind"] for d in
                     idt.compare(found["baseline"], found["candidate"])}
            self.assertIn(kind, kinds, tweak)
        extra = {REPO + "/src/C.sml": dict(
            physical=REPO + "/src/C.sml", sha256="c", bytes=1,
            related_products={})}
        found = self.closures(extra=extra)
        self.assertEqual(
            [(d["kind"], d["name"]) for d in
             idt.compare(found["baseline"], found["candidate"])],
            [("only-candidate", "shared/src/C.sml")])

    def test_a_snapshot_that_disagrees_with_the_runner_is_refused(self):
        manifest, receipt, snapshot = fake("baseline")
        snapshot["baseline"]["files"]["A.uo"][1] = "other"
        with self.assertRaises(ValueError):
            idt.closure(manifest, receipt, snapshot, "baseline")
        manifest, receipt, snapshot = fake("baseline")
        snapshot["baseline"]["files"].pop("A.uo")
        with self.assertRaises(ValueError):
            idt.closure(manifest, receipt, snapshot, "baseline")

    def test_the_repository_files_are_tracked_ones(self):
        manifest, receipt, snapshot = fake("baseline")
        found = idt.closure(manifest, receipt, snapshot, "baseline")
        manifest["selections"]["baseline"]["sources"] = [
            dict(git_path="src/simp/src/A.sml")]
        manifest["selections"]["candidate"] = \
            manifest["selections"]["baseline"]
        files = idt.repo_files(found, found, manifest, None)
        self.assertEqual(files["baseline"], ["src/B.sml",
                                             "src/simp/src/A.sml"])

    def test_a_generated_theory_is_its_script(self):
        for path, want in (
                ("src/coretypes/.hol/objs/oneTheory.sml",
                 "src/coretypes/oneScript.sml"),
                ("src/HolSat/satTheory.sig", "src/HolSat/satScript.sml"),
                ("src/postkernel/Theory.sml", "src/postkernel/Theory.sml"),
                ("src/x/Foo.sml", "src/x/Foo.sml")):
            self.assertEqual(idt.tracked(path), want)


class Work(unittest.TestCase):
    def receipt(self, consumed=7, keys=("a", "a", "b")):
        return dict(
            result=dict(observations=[["observation", k] for k in keys] +
                        [["check", "c1", True]], expected_test_count=3,
                        outcome="ok"),
            measurements=dict(
                workloads={"w": dict(batches=[
                    dict(consumed=consumed, iterations=1),
                    dict(consumed=2 * consumed, iterations=2)],
                    schedule="warmup")}, storage={"s": 1}),
            storage_graph=[1])

    def test_the_calibration_repeats_are_not_part_of_the_work(self):
        one = idt.work(self.receipt())
        two = idt.work(self.receipt(keys=("a", "b")))
        self.assertEqual(one["keys"], ["a", "b"])
        self.assertEqual(idt.work_differences(one, two), [])
        self.assertEqual(one["checks"], [["c1", True]])

    def test_a_different_consumption_is_a_difference(self):
        d = idt.work_differences(idt.work(self.receipt()),
                                 idt.work(self.receipt(consumed=8)))
        self.assertEqual([x["name"] for x in d], ["workloads"])

    def test_an_inconsistent_consumption_is_refused(self):
        r = self.receipt()
        r["measurements"]["workloads"]["w"]["batches"][1]["consumed"] = 99
        with self.assertRaises(ValueError):
            idt.work(r)


class Snapshot(unittest.TestCase):
    def test_a_product_that_names_its_directory_is_normalized(self):
        with tempfile.TemporaryDirectory() as tmp:
            rows = []
            for side in ("one", "two"):
                root = Path(tmp) / side
                root.mkdir()
                (root / "A.uo").write_text("see %s/A.sml\n" % root)
                (root / "B.sml").write_text("same\n")
                os.symlink("B.sml", root / "L")
                rows.append(snap.snapshot(root)["files"])
            self.assertNotEqual(rows[0]["A.uo"][1], rows[1]["A.uo"][1])
            self.assertEqual(rows[0]["A.uo"][2], rows[1]["A.uo"][2])
            self.assertEqual(rows[0]["L"], ["link", "B.sml"])

    def test_the_wrapper_records_a_private_tree_before_it_goes(self):
        import tempfile as tf
        with tempfile.TemporaryDirectory() as out:
            original = tf.TemporaryDirectory.cleanup
            try:
                snap.install(Path(out))
                with tf.TemporaryDirectory(prefix="simp-paired-") as d:
                    (Path(d) / "baseline").mkdir()
                    (Path(d) / "baseline" / "f").write_text("x")
            finally:
                tf.TemporaryDirectory.cleanup = original
            found = json.loads((Path(out) / snap.SNAPSHOT).read_text())
            self.assertEqual(list(found["baseline"]["files"]), ["f"])


if __name__ == "__main__":
    unittest.main()
