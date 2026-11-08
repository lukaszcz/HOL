#!/usr/bin/env python3
"""TASK31 gate 1 analysis (task31_identity.py) on synthetic closures and
work rows, and the snapshot wrapper (task31_snapshot.py) on a toy tree."""
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import task31_attribution as attr
import task31_identity as idt
import task31_snapshot as snap

REPO = "/repo"
BASE_BLOB, CAND_BLOB = "1" * 40, "2" * 40
ENTRY = dict(
    path="src/simp/src/A.sml", kind="source", baseline_blob=BASE_BLOB,
    candidate_blob=CAND_BLOB, reason="a reviewed change", gate="gate 2")


def fake(side, source="s1", uo="u1", extra=None, order=None, tamper=None):
    """(manifest, receipt, snapshot) of one side: a private source with a
    product, and a shared one. The product names the private directory, so
    its raw hash differs between the sides and its normalized one does not;
    `uo` changes its content."""
    private = "/tmp/simp-paired-x/" + side
    blob = BASE_BLOB if side == "baseline" else CAND_BLOB
    manifest = dict(
        repo=REPO, head="c" * 40, dirty=[], inputs={"i": 1}, tools={"t": 1},
        selections={side: dict(
            private=private, sources=[dict(
                git_path="src/simp/src/A.sml", git_blob=blob)],
            shared_dependencies=dict(products={}),
            fixture_products={"Fixture.sml": {}})})
    text = "A.sml at %s: %s\n" % (private, uo)
    data = text.encode()
    raw = hashlib.sha256(data).hexdigest()
    paths = {
        "%s/A.sml" % private: dict(
            physical="%s/A.sml" % private, sha256=source, bytes=3,
            related_products={"%s/A.uo" % private: dict(
                sha256=raw, bytes=len(data))}),
        REPO + "/src/B.sml": dict(
            physical=REPO + "/src/B.sml", sha256="b", bytes=1,
            related_products={})}
    use = order or ["%s/A.sml" % private, REPO + "/src/B.sml"]
    events = [["use", p] for p in use]
    events.append(["heapfile", REPO + "/src/H.sml"])
    if extra:
        paths.update(extra)
    normalized = hashlib.sha256(snap.normalize(data, [private])).hexdigest()
    files = {"A.sml": [3, source, source],
             "A.uo": [len(data), raw, normalized]}
    snapshot = {side: dict(root=private, spellings=[private], files=files,
                           texts={"A.uo": text})}
    if tamper:
        tamper(snapshot[side])
    return (manifest, dict(result=dict(events=events, paths=paths)),
            snapshot)


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
                (dict(source="s2"), "source"), (dict(uo="u2"), "product"),
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

    def test_an_order_difference_names_where_the_sequences_part(self):
        found = self.closures(order=[
            "/repo/src/B.sml", "/tmp/simp-paired-x/candidate/A.sml"])
        order = [d for d in idt.compare(found["baseline"],
                                        found["candidate"])
                 if d["kind"] == "order"][0]
        self.assertEqual((order["index"], order["baseline"],
                          order["candidate"]),
                         (0, "<private>/A.sml", "<repo>/src/B.sml"))

    def test_a_snapshot_that_disagrees_with_the_runner_is_refused(self):
        manifest, receipt, snapshot = fake("baseline")
        snapshot["baseline"]["files"]["A.uo"][1] = "other"
        with self.assertRaises(ValueError):
            idt.closure(manifest, receipt, snapshot, "baseline")
        manifest, receipt, snapshot = fake("baseline")
        snapshot["baseline"]["files"].pop("A.uo")
        with self.assertRaises(ValueError):
            idt.closure(manifest, receipt, snapshot, "baseline")

    def test_the_normalized_digest_is_derived_again_from_the_text(self):
        # An edited normalized digest, equalizing two sides that differ,
        # and an edited text, are both refused.
        def digest(side):
            return lambda r: r["files"]["A.uo"].__setitem__(2, "e" * 64)
        manifest, receipt, snapshot = fake("candidate", uo="u2",
                                           tamper=digest("candidate"))
        with self.assertRaises(ValueError):
            idt.closure(manifest, receipt, snapshot, "candidate")

        def text(r):
            r["texts"]["A.uo"] = r["texts"]["A.uo"].replace("u1", "u2")
        manifest, receipt, snapshot = fake("baseline", tamper=text)
        with self.assertRaises(ValueError):
            idt.closure(manifest, receipt, snapshot, "baseline")

        def gone(r):
            r["texts"].pop("A.uo")
        manifest, receipt, snapshot = fake("baseline", tamper=gone)
        with self.assertRaises(ValueError):
            idt.closure(manifest, receipt, snapshot, "baseline")

    def test_a_file_above_the_limit_is_raw_only(self):
        def big(r):
            r["files"]["A.uo"][0] = snap.LIMIT + 1
            r["texts"].pop("A.uo")
        manifest, receipt, snapshot = fake("baseline", tamper=big)
        info = receipt["result"]["paths"]["/tmp/simp-paired-x/baseline/"
                                          "A.sml"]["related_products"]
        for found in info.values():
            found["bytes"] = snap.LIMIT + 1
        with self.assertRaises(ValueError):  # normalized differs from raw
            idt.closure(manifest, receipt, snapshot, "baseline")

    def test_the_repository_files_are_tracked_ones(self):
        manifest, receipt, snapshot = fake("baseline")
        found = idt.closure(manifest, receipt, snapshot, "baseline")
        manifest["selections"]["candidate"] = \
            manifest["selections"]["baseline"]
        files = idt.repo_files(found, found, manifest, None)
        self.assertEqual(files["baseline"], ["src/B.sml",
                                             "src/simp/src/A.sml"])

    def test_a_private_file_that_maps_nowhere_is_refused(self):
        extra = {"/tmp/simp-paired-x/baseline/Mystery.sml": dict(
            physical="/tmp/simp-paired-x/baseline/Mystery.sml", sha256="m",
            bytes=1, related_products={})}
        manifest, receipt, snapshot = fake("baseline", extra=extra)
        snapshot["baseline"]["files"]["Mystery.sml"] = [1, "m", "m"]
        found = idt.closure(manifest, receipt, snapshot, "baseline")
        with self.assertRaises(ValueError):
            idt.files_of(dict(baseline=found, candidate=found), dict(
                manifest, selections=dict(baseline=manifest["selections"]
                                          ["baseline"],
                                          candidate=manifest["selections"]
                                          ["baseline"])))

    def test_an_installed_fixture_is_not_a_repository_file(self):
        extra = {"/tmp/simp-paired-x/baseline/Fixture.sml": dict(
            physical="/tmp/simp-paired-x/baseline/Fixture.sml", sha256="f",
            bytes=1, related_products={})}
        manifest, receipt, snapshot = fake("baseline", extra=extra)
        snapshot["baseline"]["files"]["Fixture.sml"] = [1, "f", "f"]
        found = idt.closure(manifest, receipt, snapshot, "baseline")
        manifest["selections"]["candidate"] = \
            manifest["selections"]["baseline"]
        got = idt.files_of(dict(baseline=found, candidate=found), manifest)
        self.assertEqual(got["loaded_files"]["baseline"],
                         ["src/B.sml", "src/simp/src/A.sml"])
        self.assertEqual(got["heap_files"]["baseline"], ["src/H.sml"])

    def test_a_generated_theory_is_its_script(self):
        for path, want in (
                ("src/coretypes/.hol/objs/oneTheory.sml",
                 "src/coretypes/oneScript.sml"),
                ("src/HolSat/satTheory.sig", "src/HolSat/satScript.sml"),
                ("src/postkernel/Theory.sml", "src/postkernel/Theory.sml"),
                ("src/x/Foo.sml", "src/x/Foo.sml")):
            self.assertEqual(idt.tracked(path), want)


class Cell(unittest.TestCase):
    """`cell` on synthetic folders: the attributed status, and what blocks
    it."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="task31-cell-")
        self.addCleanup(self.tmp.cleanup)
        self.folder = Path(self.tmp.name)

    def cell(self, entries=(ENTRY,), candidate=None, unequal=False,
             base_blob=BASE_BLOB, cand_blob=CAND_BLOB, order=None):
        sides = {"baseline": {}, "candidate": dict(candidate or {})}
        if order:
            sides["candidate"]["order"] = order
        manifest, receipts, snapshot = None, {}, {}
        for side in idt.SIDES:
            m, r, sn = fake(side, **sides[side])
            if manifest is None:
                manifest = m
            else:
                manifest["selections"].update(m["selections"])
            w = Work().receipt(
                consumed=8 if unequal and side == "candidate" else 7)
            w["result"] = dict(w["result"], **r["result"])
            receipts[side] = w
            snapshot.update(sn)
        manifest["selections"]["baseline"]["sources"][0]["git_blob"] = \
            base_blob
        manifest["selections"]["candidate"]["sources"][0]["git_blob"] = \
            cand_blob
        (self.folder / "manifest.json").write_text(json.dumps(manifest))
        (self.folder / idt.SNAPSHOT).write_text(json.dumps(snapshot))
        with mock.patch.object(idt, "checked", lambda *args: receipts):
            return idt.cell(self.folder, "c", 0, "b" * 40, "c" * 40, 3,
                            list(entries))

    def test_equal_sides_are_identical(self):
        row = self.cell()
        self.assertEqual((row["status"], row["attributed"]),
                         ("identical", []))
        self.assertEqual(row["head"], "c" * 40)
        self.assertEqual(row["dirty"], [])

    def test_a_reviewed_source_difference_is_attributed(self):
        row = self.cell(candidate=dict(source="s2", uo="u2"))
        self.assertEqual(row["status"], "attributed")
        self.assertEqual(row["unattributed_differences"], [])
        [one] = row["attributed"]
        self.assertEqual(
            (one["path"], one["entry"], one["kinds"], one["baseline_blob"],
             one["candidate_blob"], one["reason"]),
            ("src/simp/src/A.sml", "private/A.sml", ["product", "source"],
             BASE_BLOB, CAND_BLOB, "a reviewed change"))
        self.assertEqual((one["baseline_sha256"], one["candidate_sha256"]),
                         ("s1", "s2"))
        self.assertEqual(row["attribution_table"],
                         attr.digest([ENTRY]))

    def test_an_unreviewed_difference_is_different(self):
        row = self.cell(entries=(), candidate=dict(source="s2"))
        self.assertEqual(row["status"], "different")
        self.assertEqual(len(row["unattributed_differences"]), 1)

    def test_other_blobs_than_the_reviewed_pair_are_different(self):
        row = self.cell(candidate=dict(source="s2"), cand_blob="3" * 40)
        self.assertEqual(row["status"], "different")
        row = self.cell(candidate=dict(source="s2"), base_blob="4" * 40)
        self.assertEqual(row["status"], "different")

    def test_a_heap_or_build_entry_does_not_attribute_a_closure(self):
        for kind in ("heap", "build"):
            row = self.cell(entries=[dict(ENTRY, kind=kind)],
                            candidate=dict(source="s2"))
            self.assertEqual(row["status"], "different", kind)

    def test_order_and_extra_files_and_work_are_never_attributed(self):
        row = self.cell(candidate=dict(source="s2"), order=[
            "/repo/src/B.sml", "/tmp/simp-paired-x/candidate/A.sml"])
        self.assertEqual(row["status"], "different")
        self.assertIn("order", {d["kind"] for d in
                                row["unattributed_differences"]})
        extra = {REPO + "/src/C.sml": dict(
            physical=REPO + "/src/C.sml", sha256="c", bytes=1,
            related_products={})}
        row = self.cell(candidate=dict(source="s2", extra=extra))
        self.assertEqual(row["status"], "different")
        row = self.cell(candidate=dict(source="s2"), unequal=True)
        self.assertEqual(row["status"], "different")


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
