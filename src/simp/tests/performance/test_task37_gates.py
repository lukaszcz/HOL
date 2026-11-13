#!/usr/bin/env python3
"""The TASK37 disposition's gate inputs (task37_dispose.py and
task37_gates.py): the counts-file revision route, the per-gate loading
ledgers, the startup attempts ledger and the declared load deltas, and the
api-audit receipt that must be present."""
import argparse
import json
from pathlib import Path
import tempfile
import types
import unittest
from unittest import mock

import acceptance as a
import task37_dispose as d
import task37_gates as gates


def write(path, value):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(value if isinstance(value, str)
                          else json.dumps(value))
    return Path(path)


class Counts(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        patch = mock.patch.object(d, "COUNTS_DIR", self.root)
        patch.start()
        self.addCleanup(patch.stop)
        self.first = write(self.root / "t_iterations.json", "one")
        self.second = write(self.root / "t_iterations_rev1.json", "two")
        self.table = types.SimpleNamespace(
            files=lambda: (self.first, self.second))

    def stage(self, name, path):
        inventory = dict(counts_file=name, iterations_seal=a.seal(path))
        return dict(inventory=inventory, first_inventory=inventory)

    def test_the_counts_file_or_a_revision_of_it_is_accepted(self):
        for path in (self.first, self.second):
            got = d.check_counts(self.stage(path.name, path), "t",
                                 self.table)
            self.assertEqual(got, a.seal(path))

    def test_another_name_or_a_stale_file_is_refused(self):
        other = write(self.root / "other.json", "x")
        with self.assertRaisesRegex(ValueError, "not one of"):
            d.check_counts(self.stage(other.name, other), "t", self.table)
        stage = self.stage(self.second.name, self.second)
        self.second.write_text("changed")
        with self.assertRaisesRegex(ValueError, "stale"):
            d.check_counts(stage, "t", self.table)


class LoadingLedgers(unittest.TestCase):
    def read(self, values):
        args = argparse.Namespace(loading_ledger=values)
        return d.read_gates(args, None, {}, [], {})

    def test_one_ledger_for_each_gate_is_required(self):
        for values, text in (
                (None, "is needed for each loading gate"),
                (["simplib=x"], "is needed for each loading gate"),
                (["simplib=x", "simplib=y"], "twice"),
                (["simplib=x", "other=y"], "needs KEY=PATH"),
                (["x"], "needs KEY=PATH")):
            with self.assertRaisesRegex(ValueError, text):
                self.read(values)

    def test_the_parser_takes_the_repeatable_option(self):
        args = d.parser().parse_args(
            ["--candidate", "c" * 10, "--record", "o", "--loading-ledger",
             "simplib=a", "--loading-ledger", "conglib=b",
             "--startup-ledger", "l", "--startup-declared", "s"])
        self.assertEqual(args.loading_ledger, ["simplib=a", "conglib=b"])
        self.assertEqual(args.startup_ledger, Path("l"))


class StartupLedger(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()

    def ledger(self, *lines):
        return write(self.root / "attempts.jsonl", "".join(
            json.dumps(x) + "\n" for x in lines))

    def run_dir(self, name):
        path = self.root / name
        (path / "gate").mkdir(parents=True)
        return path

    def test_every_attempt_is_listed_and_the_judged_one_is_last(self):
        one, two = self.run_dir("one"), self.run_dir("two")
        ledger = self.ledger(
            dict(event="open", attempt="one", output=str(one)),
            dict(event="close", attempt="one", output=str(one), exit=1),
            dict(event="open", attempt="two", output=str(two)),
            dict(event="close", attempt="two", output=str(two), exit=0))
        got = gates.startup_attempts(ledger, two / "gate")
        self.assertEqual([(x["attempt"], x["status"], x["judged"])
                          for x in got],
                         [("one", "failed", False), ("two", "ok", True)])

    def test_a_judged_gate_that_is_not_the_last_attempt_is_refused(self):
        one, two = self.run_dir("one"), self.run_dir("two")
        ledger = self.ledger(
            dict(event="open", attempt="one", output=str(one)),
            dict(event="close", attempt="one", output=str(one), exit=0),
            dict(event="open", attempt="two", output=str(two)),
            dict(event="close", attempt="two", output=str(two), exit=1))
        with self.assertRaisesRegex(ValueError, "not in the last"):
            gates.startup_attempts(ledger, one / "gate")

    def test_an_open_last_attempt_or_a_bad_ledger_is_refused(self):
        one = self.run_dir("one")
        with self.assertRaisesRegex(ValueError, "not closed"):
            gates.startup_attempts(self.ledger(
                dict(event="open", attempt="one", output=str(one))),
                one / "gate")
        with self.assertRaisesRegex(ValueError, "no startup attempts"):
            gates.startup_attempts(self.root / "none", one / "gate")
        with self.assertRaisesRegex(ValueError, "no attempt"):
            gates.startup_attempts(self.ledger(), one / "gate")
        with self.assertRaisesRegex(ValueError, "without a single"):
            gates.startup_attempts(self.ledger(
                dict(event="close", attempt="one", output=str(one),
                     exit=0)), one / "gate")
        with self.assertRaisesRegex(ValueError, "opened twice"):
            gates.startup_attempts(self.ledger(
                dict(event="open", attempt="one", output=str(one)),
                dict(event="open", attempt="one", output=str(one))),
                one / "gate")
        write(self.root / "bad.jsonl", "not json\n")
        with self.assertRaisesRegex(ValueError, "not JSON"):
            gates.startup_attempts(self.root / "bad.jsonl", one / "gate")


class Declared(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.header = dict(record_sha256="a" * 64)
        self.doc = dict(
            schema=gates.DECLARED_SCHEMA, record_sha256="a" * 64,
            totals={"load-simpLib": 158440, "load-congLib": 90000},
            archive="/x/round4/gate", archive_sha256="b" * 64)

    def decisions(self, simp=158440, cong=90000, images=("b1", "s1")):
        return dict(R2={
            "load-simpLib": {i: dict(load=dict(total=simp))
                             for i in images},
            "load-congLib": {i: dict(load=dict(total=cong))
                             for i in images}})

    def test_the_sidecar_is_bound_to_the_record(self):
        path = write(self.root / "declared.json", self.doc)
        got, seal = gates.read_declared(path, self.header)
        self.assertEqual(got["totals"], self.doc["totals"])
        self.assertEqual(seal, a.seal(path))
        with self.assertRaisesRegex(ValueError, "not those of the record"):
            gates.read_declared(path, dict(record_sha256="c" * 64))
        for bad in (dict(self.doc, totals={"load-simpLib": 1}),
                    dict(self.doc, schema="x"),
                    dict(self.doc, archive="")):
            write(self.root / "bad.json", bad)
            with self.assertRaises(ValueError):
                gates.read_declared(self.root / "bad.json", self.header)

    def test_equal_totals_on_every_image_are_no_problem(self):
        self.assertEqual(gates.declared_problems(
            self.doc, self.decisions()), [])

    def test_a_different_total_on_any_image_is_a_problem_and_fails(self):
        decisions = self.decisions()
        decisions["R2"]["load-congLib"]["s1"]["load"]["total"] += 1
        problems = gates.declared_problems(self.doc, decisions)
        self.assertEqual(len(problems), 1)
        self.assertIn("load-congLib on image s1", problems[0])
        record = gates.startup_gate(
            self.header, dict(decision="pass"), dict(decision="pass"),
            problems)
        self.assertEqual((record["source"], record["exit"]), ("fail", 1))
        self.assertTrue(record["failed"])
        self.assertIn("declared deltas", " ".join(record["reasons"]))
        self.assertTrue(gates.declared_problems(self.doc, {}))
        self.assertTrue(gates.declared_problems(
            self.doc, dict(R2={"load-simpLib": {}})))


class AuditReceipt(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def gate(self, **receipt):
        path = write(self.root / "receipt.json", dict(
            {"pass": True, "cases": list(range(8))}, **receipt))
        return dict(receipt=str(path), seal=a.seal(path))

    def test_a_present_passing_receipt_is_accepted(self):
        gates.check_audit_receipt("loading-simpLib", self.gate())

    def test_a_missing_changed_or_failing_receipt_is_refused(self):
        found = self.gate()
        Path(found["receipt"]).unlink()
        with self.assertRaisesRegex(ValueError, "receipt is missing"):
            gates.check_audit_receipt("loading-simpLib", found)
        found = self.gate()
        Path(found["receipt"]).write_text(json.dumps(
            {"pass": True, "cases": list(range(8)), "x": 1}))
        with self.assertRaisesRegex(ValueError, "differs from its seal"):
            gates.check_audit_receipt("loading-simpLib", found)
        with self.assertRaisesRegex(ValueError, "did not pass"):
            gates.check_audit_receipt("loading-simpLib",
                                      self.gate(**{"pass": False}))
        with self.assertRaisesRegex(ValueError, "did not pass"):
            gates.check_audit_receipt("loading-simpLib",
                                      self.gate(cases=[1]))

    def test_check_one_audit_requires_the_receipt_file(self):
        one = self.gate()
        reports = {g: dict(semantic_gate=one) for g in gates.LOADING}
        self.assertEqual(gates.check_one_audit(reports), one["seal"])
        Path(one["receipt"]).unlink()
        with self.assertRaisesRegex(ValueError, "receipt is missing"):
            gates.check_one_audit(reports)


if __name__ == "__main__":
    unittest.main()
