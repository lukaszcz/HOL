#!/usr/bin/env python3
"""The TASK37 disposition's gate inputs (task37_dispose.py and
task37_gates.py): the counts-file revision route, the per-gate loading
ledgers, the startup attempts ledger and the declared load deltas, and the
api-audit receipt that must be present."""
import argparse
import hashlib
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


def r2(simp=158440, cong=90000, images=("b1", "s1")):
    """The R2 load totals of a gate's decisions."""
    return {"load-simpLib": {i: dict(load=dict(total=simp))
                             for i in images},
            "load-congLib": {i: dict(load=dict(total=cong))
                             for i in images}}


class StartupLedger(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()

    def ledger(self, *lines):
        return write(self.root / "attempts.jsonl", "".join(
            json.dumps(x) + "\n" for x in lines))

    def run_dir(self, name, done=True, decision=None, declared=None,
                reasons=()):
        """An attempt's output: `done`, the gate's decisions (the gate
        decision with R2 totals, if any) and its sidecar."""
        path = self.root / name
        (path / "gate").mkdir(parents=True)
        if done:
            write(path / "done", "done\n")
        if decision is not None:
            write(path / "gate" / "decisions.json", dict(
                decision=decision, reasons=list(reasons), blockers=[],
                R2=r2()))
        if declared is not None:
            record = write(path / "not-client-visible.md", "record\n")
            rsha = hashlib.sha256(record.read_bytes()).hexdigest()
            write(path / "gate" / "header.json", dict(record_sha256=rsha))
            side = write(path / "declared-deltas.json", dict(
                record_sha256=rsha,
                totals={"load-simpLib": declared[0],
                        "load-congLib": declared[1]},
                archive="/x/round4/gate"))
            write(path / "inputs.txt", "A=b\nDECLARED_DELTAS_SHA256=%s\n"
                  % hashlib.sha256(side.read_bytes()).hexdigest())
        return path

    def attempts(self, *rows):
        """A ledger of (name, exit) attempts, each opened and closed."""
        lines = []
        for name, exit_ in rows:
            out = str(self.root / name)
            lines.append(dict(event="open", attempt=name, output=out))
            if exit_ is not None:
                lines.append(dict(event="close", attempt=name, output=out,
                                  exit=exit_))
        return self.ledger(*lines)

    def test_every_attempt_is_listed_and_the_judged_one_is_last(self):
        one, two = self.run_dir("one", done=False), self.run_dir("two")
        got = gates.startup_attempts(
            self.attempts(("one", 1), ("two", 0)), two / "gate")
        self.assertEqual([(x["attempt"], x["status"], x["judged"],
                           x["verdict"]) for x in got],
                         [("one", "failed", False, "void"),
                          ("two", "ok", True, "judged")])

    def test_a_run_that_completed_with_a_soft_failure_is_judged(self):
        two = self.run_dir("two")
        got = gates.startup_attempts(self.attempts(("two", 2)),
                                     two / "gate")
        self.assertEqual((got[-1]["status"], got[-1]["exit"]),
                         ("soft", 2))

    def test_an_incomplete_judged_attempt_is_void_and_refused(self):
        for name, exit_, done in (
                ("a", 2, False),     # a step that failed with 2: no done
                ("b", 0, False), ("c", 1, True), ("d", 143, True),
                ("e", 130, True), ("f", 129, True), ("g", 3, True)):
            out = self.run_dir(name, done=done)
            with self.assertRaisesRegex(ValueError, "void", msg=name):
                gates.startup_attempts(self.attempts((name, exit_)),
                                       out / "gate")

    def test_a_judged_gate_that_is_not_the_last_attempt_is_refused(self):
        one, two = self.run_dir("one"), self.run_dir("two")
        ledger = self.attempts(("one", 0), ("two", 1))
        with self.assertRaisesRegex(ValueError, "not in the last"):
            gates.startup_attempts(ledger, one / "gate")

    def test_an_open_last_attempt_or_a_bad_ledger_is_refused(self):
        one = self.run_dir("one")
        with self.assertRaisesRegex(ValueError, "not closed"):
            gates.startup_attempts(self.attempts(("one", None)),
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

    def judged(self, *rows):
        last = self.run_dir("last")
        return gates.startup_attempts(
            self.attempts(*rows, ("last", 0)), last / "gate")

    def test_a_redraw_after_a_void_attempt_is_accepted(self):
        # void: the attempt left no gate decision, whatever its exit
        self.run_dir("signal", done=True)                  # exit 143
        self.run_dir("nodone", done=False)                 # exit 0
        self.run_dir("crashed")                            # no decisions
        self.run_dir("killed")                             # never closed
        got = self.judged(("signal", 143), ("nodone", 0), ("crashed", 2),
                          ("killed", None))
        self.assertEqual([x["verdict"] for x in got],
                         ["void", "void", "void", "void", "judged"])

    def test_an_incomplete_attempt_is_judged_by_its_gate_decision(self):
        # a decided gate is not undone by a crash or a signal after it
        for name, exit_, done, decision, reasons in (
                ("p1", 0, False, "pass", ()),        # passing: superseded
                ("p2", 143, True, "pass", ()),
                ("f1", 1, False, "fail", ("R1 differs",)),  # non-delta
                ("f2", 130, False, "attributed", ("R3 noise",))):
            self.run_dir(name, done=done, decision=decision,
                         reasons=reasons, declared=(158440, 90000))
            with self.assertRaisesRegex(ValueError, "stays judged",
                                        msg=name):
                self.judged((name, exit_))
            import shutil
            shutil.rmtree(self.root / name)
            shutil.rmtree(self.root / "last", ignore_errors=True)

    def test_an_incomplete_attempt_that_failed_on_the_declared_deltas(
            self):
        self.run_dir("cut", done=False, decision="pass",
                     declared=(158441, 90000))
        got = self.judged(("cut", 143))
        self.assertEqual((got[0]["verdict"], got[0]["complete"]),
                         ("declared-deltas", False))

    def test_a_redraw_after_a_gate_that_failed_on_the_declared_deltas(
            self):
        # the gate itself found nothing, the totals differ from the
        # record's own sidecar: the declared deltas failed
        self.run_dir("d1", decision="pass", declared=(158441, 90000))
        self.run_dir("d2", decision="attributed", declared=(158440, 1))
        got = self.judged(("d1", 2), ("d2", 2))
        self.assertEqual([x["verdict"] for x in got[:2]],
                         ["declared-deltas"] * 2)
        self.assertEqual((got[0]["decision"], got[0]["reasons"]),
                         ("pass", []))
        self.assertIn("load-simpLib", got[0]["problems"][0])
        self.assertIn("load-congLib", got[1]["problems"][0])

    def test_a_swapped_sidecar_of_an_earlier_attempt_is_refused(self):
        import shutil
        other = self.run_dir("other", decision="pass",
                             declared=(158441, 90000))
        for what, text in (
                ("sidecar", "not that of its record"),
                ("record", "not that of its record"),
                ("inputs", "sealed inputs.txt")):
            run = self.run_dir("d1", decision="pass",
                               declared=(158441, 90000))
            if what == "sidecar":      # another attempt's sidecar
                shutil.copy(other / "declared-deltas.json",
                            run / "declared-deltas.json")
                doc = a.load(run / "declared-deltas.json")
                doc["record_sha256"] = "0" * 64
                write(run / "declared-deltas.json", doc)
            elif what == "record":
                write(run / "not-client-visible.md", "edited\n")
            else:                      # edited sidecar, same record
                doc = a.load(run / "declared-deltas.json")
                doc["totals"]["load-simpLib"] = 158440
                write(run / "declared-deltas.json", doc)
            with self.assertRaisesRegex(ValueError, text, msg=what):
                self.judged(("d1", 2))
            shutil.rmtree(run)
            shutil.rmtree(self.root / "last", ignore_errors=True)

    def test_a_redraw_after_any_other_completed_gate_is_refused(self):
        for decision, reasons, declared in (
                ("pass", (), (158440, 90000)),   # nothing wrong
                ("attributed", (), (158440, 90000)),
                ("fail", ("R1 differs",), (158441, 90000)),
                ("pass", ("R3 noise",), (158441, 90000)),
                ("fail", (), (158441, 90000)),   # not a pass/attributed
                ("blocked", (), (158441, 90000)),
                ("smoke", (), (158441, 90000)),
                ("pass", (), None)):             # no sidecar to show it
            self.run_dir("bad", decision=decision, reasons=reasons,
                         declared=declared)
            with self.assertRaisesRegex(
                    ValueError, "stays judged", msg=(decision, reasons)):
                self.judged(("bad", 2))
            import shutil
            shutil.rmtree(self.root / "bad")
            shutil.rmtree(self.root / "last", ignore_errors=True)


def archive_fixture(root, simp=158440, cong=90000, name="round4",
                    prefix=""):
    """A gate archive with R2 totals, a record text that declares them from
    it, and the sidecar `fill_record.py` writes: (archive, record, sidecar,
    header)."""
    archive = Path(root) / name / "gate"
    write(archive / "decisions.json", dict(R2=r2(simp, cong)))
    sha = hashlib.sha256((archive / "decisions.json").read_bytes()
                         ).hexdigest()
    record = write(Path(root) / "not-client-visible.md",
                   prefix + "Ds and Dc are DECLARED (TESTED in the archive\n"
                   "    %s (sha256 of its decisions.json %s): Ds = %s, "
                   "Dc = %s)\n" % (archive, sha, format(simp, ","),
                                    format(cong, ",")))
    rsha = hashlib.sha256(record.read_bytes()).hexdigest()
    side = write(Path(root) / "declared-deltas.json", dict(
        schema=gates.DECLARED_SCHEMA, record_sha256=rsha,
        totals={"load-simpLib": simp, "load-congLib": cong},
        archive=str(archive), archive_sha256=sha))
    return archive, record, side, dict(record_sha256=rsha)


class Declared(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.archive, self.record, self.side,
         self.header) = archive_fixture(self.root)
        self.doc = json.loads(self.side.read_text())

    def decisions(self, simp=158440, cong=90000):
        return dict(R2=r2(simp, cong))

    def read(self, **changes):
        write(self.side, dict(self.doc, **changes))
        return gates.read_declared(self.side, self.header, self.record)

    def test_the_sidecar_is_bound_to_the_record_and_its_content(self):
        got, seal = self.read()
        self.assertEqual(got["totals"], self.doc["totals"])
        self.assertEqual(seal, a.seal(self.side))
        with self.assertRaisesRegex(ValueError, "not those of the record"):
            gates.read_declared(self.side, dict(record_sha256="c" * 64),
                                self.record)
        self.assertEqual(gates.declared_problems(
            got, self.decisions()), [])

    def test_a_malformed_sidecar_is_refused(self):
        for bad in (dict(totals={"load-simpLib": 1}), dict(schema="x"),
                    dict(archive=""), dict(archive_sha256="b" * 10),
                    dict(archive_sha256=5),
                    dict(totals={"load-simpLib": True,
                                 "load-congLib": 90000})):
            with self.assertRaises(ValueError, msg=bad):
                self.read(**bad)

    def test_edited_totals_are_refused(self):
        """The totals are recomputed from the archive named."""
        with self.assertRaisesRegex(ValueError, "not the R2 load totals"):
            self.read(totals={"load-simpLib": 158441,
                              "load-congLib": 90000})
        with self.assertRaisesRegex(ValueError, "not the R2 load totals"):
            self.read(totals={"load-simpLib": 158440, "load-congLib": 9})

    def test_another_or_changed_archive_is_refused(self):
        other, _, _, _ = archive_fixture(self.root / "x", 1, 2, "other")
        with self.assertRaisesRegex(ValueError, "sha256 differs"):
            self.read(archive=str(other))
        write(self.archive / "decisions.json", dict(R2=r2(5, 6)))
        with self.assertRaisesRegex(ValueError, "sha256 differs"):
            self.read()
        with self.assertRaisesRegex(ValueError, "is missing"):
            self.read(archive=str(self.root / "nowhere"))

    def test_an_archive_whose_totals_differ_between_images_is_refused(self):
        bad = r2()
        bad["load-congLib"]["s1"]["load"]["total"] = 1
        write(self.archive / "decisions.json", dict(R2=bad))
        sha = hashlib.sha256((self.archive / "decisions.json"
                              ).read_bytes()).hexdigest()
        with self.assertRaisesRegex(ValueError, "not one integer"):
            self.read(archive_sha256=sha)

    def test_a_record_text_that_declares_otherwise_is_refused(self):
        text = self.record.read_text()
        for old, new, message in (
                ("Ds = 158,440", "Ds = 158,441", "does not declare Ds"),
                ("Dc = 90,000", "Dc = 91,000", "does not declare Ds"),
                (str(self.archive), str(self.root / "elsewhere"),
                 "does not name the archive")):
            self.record.write_text(text.replace(old, new))
            header = dict(record_sha256=hashlib.sha256(
                self.record.read_bytes()).hexdigest())
            write(self.side, dict(self.doc, record_sha256=header[
                "record_sha256"]))
            with self.assertRaisesRegex(ValueError, message):
                gates.read_declared(self.side, header, self.record)
        # the archive sha the text names is another
        self.record.write_text(text.replace(self.doc["archive_sha256"],
                                            "9" * 64))
        header = dict(record_sha256=hashlib.sha256(
            self.record.read_bytes()).hexdigest())
        write(self.side, dict(self.doc, record_sha256=header[
            "record_sha256"]))
        with self.assertRaisesRegex(ValueError, "does not name the arch"):
            gates.read_declared(self.side, header, self.record)
        # no record text given
        with self.assertRaisesRegex(ValueError, "pass the record"):
            gates.read_declared(self.side, header)

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


class StartupPath(unittest.TestCase):
    """`read_gates` over a startup attempt: the gate and its null control
    in one attempt, the ledger and its `done` sealed, the declared deltas
    judged. The loading side is stood in for."""

    class Lineage:
        tree = "t"

        def commit(self, label, rev):
            return rev

        def equivalent(self, label, rev):
            return rev

        def candidate_of(self, label, rev):
            return rev

        def harness(self, label, found, clean=False):
            return found["head"]

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.cand = "c" * 40
        (self.archive, self.record, self.side,
         self.header) = archive_fixture(
             self.root / "decl", prefix="Baseline: develop %s\n%s\n" % (
                 a.BASE, self.cand))
        self.ev = self.root / "attempt"
        for patch in (
                mock.patch.object(gates, "read_loading", lambda out, gate,
                                  lineage: (dict(stage="second"), "pass")),
                mock.patch.object(gates, "check_one_audit",
                                  lambda reports: {"sha256": "x"}),
                mock.patch.object(gates, "replay_loading"),
                mock.patch.object(gates, "replay_startup")):
            patch.start()
            self.addCleanup(patch.stop)

    def archive_of(self, directory, null, total=(158440, 90000)):
        import startup_gate as sg
        trees = {"b1": dict(rev=a.BASE), "b2": dict(rev=a.BASE),
                 "s1": dict(rev=a.BASE if null else self.cand),
                 "s2": dict(rev=a.BASE if null else self.cand)}
        sha = self.header["record_sha256"]
        write(directory / "header.json", dict(
            schema=sg.SCHEMA, null=null, pairs=sg.PAIRS,
            record_sha256=None if null else sha, trees=trees,
            sides=dict(base=["b1", "b2"], candidate=["s1", "s2"]),
            harness=dict(head=self.cand, tree_outside_performance="t",
                         dirty=False)))
        write(directory / "decisions.json", dict(
            decision="pass", R2=r2(*total)))

    def make(self, exit_=0, total=(158440, 90000), done=True):
        self.ev.mkdir(exist_ok=True)
        self.archive_of(self.ev / "gate", False, total)
        self.archive_of(self.ev / "gate-null", True)
        if done:
            write(self.ev / "done", "done\n")
        ledger = write(self.root / "attempts.jsonl", json.dumps(dict(
            event="open", attempt="attempt", output=str(self.ev))) + "\n"
            + json.dumps(dict(event="close", attempt="attempt",
                              output=str(self.ev), exit=exit_)) + "\n")
        loading = [self.root / "ls", self.root / "lc"]
        for each in loading:
            write(each / "loading.json", {})
            write(self.root / (each.name + ".ledger"), "")
        return argparse.Namespace(
            loading_ledger=["simplib=%s" % (self.root / "ls.ledger"),
                            "conglib=%s" % (self.root / "lc.ledger")],
            startup_gate=self.ev / "gate", startup_null=self.ev /
            "gate-null", startup_record=self.record,
            startup_declared=self.side, startup_ledger=ledger,
            loading_simplib=loading[0], loading_conglib=loading[1],
            d7_build=None)

    def read(self, args):
        inputs, late, extra = {}, [], {}
        found, _ = d.read_gates(args, self.Lineage(), inputs, late, extra)
        return found, inputs, late, extra

    def test_a_completed_attempt_is_read_and_sealed(self):
        args = self.make()
        found, inputs, late, extra = self.read(args)
        record = found[gates.STARTUP]
        self.assertEqual(record["source"], "pass")
        self.assertEqual(set(inputs[gates.STARTUP]), {
            "header", "decisions", "null-header", "null-decisions",
            "record", "declared", "ledger", "done"})
        self.assertEqual(inputs[gates.STARTUP]["ledger"],
                         a.seal(args.startup_ledger))
        self.assertEqual(inputs[gates.STARTUP]["done"],
                         a.seal(self.ev / "done"))
        self.assertEqual(extra["startup_declared"]["problems"], [])
        self.assertEqual([(x["attempt"], x["judged"])
                          for x in extra["startup_attempts"]],
                         [("attempt", True)])
        self.assertEqual(len(late), 3)    # the gate and both loadings

    def test_a_soft_failure_exit_2_is_judged_and_the_totals_decide(self):
        args = self.make(exit_=2, total=(158441, 90000))
        found, _, _, extra = self.read(args)
        record = found[gates.STARTUP]
        self.assertEqual((record["source"], record["exit"]), ("fail", 1))
        self.assertEqual(len(extra["startup_declared"]["problems"]), 2)
        self.assertIn("declared deltas", " ".join(record["reasons"]))

    def test_an_incomplete_attempt_cannot_be_judged(self):
        with self.assertRaisesRegex(ValueError, "void"):
            self.read(self.make(done=False))
        with self.assertRaisesRegex(ValueError, "void"):
            self.read(self.make(exit_=143))

    def test_the_gate_and_its_null_control_must_be_of_one_attempt(self):
        args = self.make()
        other = self.root / "other"
        other.mkdir()
        self.archive_of(other / "gate-null", True)
        args.startup_null = other / "gate-null"
        with self.assertRaisesRegex(ValueError, "not of one attempt"):
            self.read(args)

    def test_a_tampered_sidecar_or_record_is_refused(self):
        args = self.make()
        doc = json.loads(self.side.read_text())
        write(self.side, dict(doc, totals={"load-simpLib": 1,
                                           "load-congLib": 90000}))
        with self.assertRaisesRegex(ValueError, "not the R2 load totals"):
            self.read(args)
        write(self.side, doc)
        self.record.write_text(self.record.read_text() + "x")
        with self.assertRaisesRegex(ValueError, "differs from its seal"):
            self.read(args)


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
