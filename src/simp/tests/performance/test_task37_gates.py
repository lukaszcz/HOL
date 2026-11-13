#!/usr/bin/env python3
"""The TASK37 disposition's gate inputs (task37_dispose.py and
task37_gates.py): the counts-file revision route, the per-gate loading
ledgers, the startup attempts ledger and the declared load deltas, and the
api-audit receipt that must be present."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import types
import unittest
from unittest import mock

import acceptance as a
import test_startup_gate as tsg
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


def seal_gate(directory):
    """The `receipt.json` of a gate archive (`startup_gate.write_archive`)
    for its header and decisions."""
    directory = Path(directory)
    if not (directory / "header.json").exists():
        write(directory / "header.json", {})
    write(directory / "receipt.json", {
        n: hashlib.sha256((directory / n).read_bytes()).hexdigest()
        for n in ("header.json", "decisions.json")})


def fake_replays(out, record=None, null=False, module=None):
    """Stands in for `gates.replays` over the fake gate archives of these
    fixtures: they replay unless they hold a `no-replay` marker. The real
    archives are those of `ReplayValidity`."""
    if (Path(out) / "no-replay").exists():
        return False, "marked as not replaying"
    return True, ""


REPLAYED = {"replay-gate.exit": "exit=0\n"}
# the status files of a run that got to its end (run_startup_gate.sh)
FINISHED = {n + ".exit": "exit=0\n" for n in gates.SOFT_STEPS +
            gates.HARD_STEPS}


HARNESS = "ab" * 20


class Ledgers(unittest.TestCase):
    """A directory of attempts and their ledger. The harness commit an
    attempt records (`harness-head.txt`, `HARNESS`) has the checkout's
    `startup_gate.py`, unless a test says otherwise (`self.frozen`)."""
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        import startup_gate as sg
        self.frozen = Path(sg.__file__).read_bytes()
        self.real_harness_source = gates.harness_source
        patch = mock.patch.object(gates, "harness_source",
                                  lambda head: self.frozen)
        patch.start()
        self.addCleanup(patch.stop)

    def ledger(self, *lines):
        return write(self.root / "attempts.jsonl", "".join(
            json.dumps(x) + "\n" for x in lines))

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


class StartupLedger(Ledgers):
    def setUp(self):
        super().setUp()
        patch = mock.patch.object(gates, "replays", fake_replays)
        patch.start()
        self.addCleanup(patch.stop)

    def run_dir(self, name, done=True, decision=None, declared=None,
                reasons=(), replays=True, steps=None):
        """An attempt's output: `done`, the gate's decisions (the gate
        decision with R2 totals, if any), its sidecar, the files of the
        runner's steps (`steps`: name -> text) and, with `replays` false,
        a gate archive that does not replay."""
        path = self.root / name
        (path / "gate").mkdir(parents=True)
        write(path / "harness-head.txt", HARNESS + "\n")
        if done:
            write(path / "done", "done\n")
            steps = dict(FINISHED, **(steps or {}))
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
        if decision is not None:
            seal_gate(path / "gate")
            if not replays:
                write(path / "gate" / "no-replay", "")
        for step, text in (steps or {}).items():
            write(path / step, text)
        return path

    def test_every_attempt_is_listed_and_the_judged_one_is_last(self):
        one = self.run_dir("one", done=False)
        two = self.run_dir("two", decision="pass")
        got = gates.startup_attempts(
            self.attempts(("one", 1), ("two", 0)), two / "gate")
        self.assertEqual([(x["attempt"], x["status"], x["judged"],
                           x["verdict"]) for x in got],
                         [("one", "failed", False, "void"),
                          ("two", "ok", True, "judged")])

    def test_a_run_that_completed_with_a_soft_failure_is_judged(self):
        two = self.run_dir("two", decision="pass")
        got = gates.startup_attempts(self.attempts(("two", 2)),
                                     two / "gate")
        self.assertEqual((got[-1]["status"], got[-1]["exit"]),
                         ("soft", 2))

    def test_an_incomplete_judged_attempt_is_void_and_refused(self):
        for name, exit_ in (
                ("a", 2),            # a hard step failed with 2: no done
                ("c", 1), ("d", 143), ("e", 130), ("f", 129), ("g", 3)):
            out = self.run_dir(name, done=False, steps={
                "build.exit": "exit=%d\n" % exit_})
            with self.assertRaisesRegex(ValueError, "void", msg=name):
                gates.startup_attempts(self.attempts((name, exit_)),
                                       out / "gate")

    def test_a_closing_status_that_contradicts_the_files_is_damage(self):
        damaged = "wrote no `done`"
        hard = {"cell-o1-24.exit": "exit=2\n"}
        soft = {"who_pays_s1.exit": "exit=2\n", "gate.exit": "exit=0\n"}
        # (close status, step files over the finished run, damaged?)
        cases = []
        for exit_ in (0, 2):
            cases += [(exit_, {}, True), (exit_, soft, True)]
        cases += [(0, hard, True)]
        cases += [(2, hard, False), (2, dict(hard, **soft), False),
                  (2, {"build.exit": "exit=2\n"}, False)]
        for exit_ in (1, 143, 130, None):
            cases += [(exit_, {}, False), (exit_, soft, False),
                      (exit_, hard, False)]
        for exit_, steps, bad in cases:
            for as_last in (False, True):
                case = (exit_, sorted(steps), as_last)
                out = self.run_dir("y", done=True, decision="fail",
                                   reasons=("R1 differs",), steps=steps,
                                   declared=(158440, 90000))
                (out / "done").unlink()     # the files of a finished run
                if as_last:
                    ledger, judged = self.attempts(("y", exit_)), out
                else:
                    judged = self.run_dir(
                        "last", done=True, decision="pass",
                        declared=(158440, 90000))
                    ledger = self.attempts(("y", exit_), ("last", 0))
                got = gates.classify(dict(
                    attempt="y", output=str(out), exit=exit_,
                    status="soft"))
                self.assertEqual(bool(got["damaged"]), bad, case)
                self.assertEqual(got["kind"], "fail")     # still decided
                if bad:
                    with self.assertRaisesRegex(ValueError, damaged,
                                                msg=case):
                        gates.startup_attempts(ledger, judged / "gate")
                elif as_last:
                    self.assertEqual(gates.startup_attempts(
                        ledger, judged / "gate")[-1]["verdict"],
                        "judged-incomplete", case)
                shutil.rmtree(out)
                shutil.rmtree(self.root / "last", ignore_errors=True)
        # exit 0 with no step file at all (done and the last cell gone)
        out = self.run_dir("z", done=False, decision="pass",
                           declared=(158440, 90000))
        with self.assertRaisesRegex(ValueError, damaged):
            gates.startup_attempts(self.attempts(("z", 0)), out / "gate")

    def test_done_makes_an_attempt_complete_whatever_its_close_status(self):
        for exit_ in (129, 130, 143, 1, None):
            out = self.run_dir("s", done=True, decision="pass",
                               declared=(158440, 90000))
            got = gates.startup_attempts(self.attempts(("s", exit_)),
                                         out / "gate")[-1]
            self.assertEqual(got["verdict"], "judged", exit_)
            # a complete earlier attempt that passed blocks the redraw
            with self.assertRaisesRegex(ValueError, "stays judged",
                                        msg=exit_):
                self.judged(("s", exit_))
            # and its gate must replay, else it is damaged
            (out / "gate" / "no-replay").write_text("")
            with self.assertRaisesRegex(ValueError, "damaged after the "
                                        "run", msg=exit_):
                gates.startup_attempts(self.attempts(("s", exit_)),
                                       out / "gate")
            shutil.rmtree(out)
            shutil.rmtree(self.root / "last", ignore_errors=True)

    def test_an_unreadable_harness_is_refused_with_commit_and_path(self):
        out = self.run_dir("a", done=False, decision="fail",
                           reasons=("R1 differs",), declared=(158440, 90000))
        ledger = self.attempts(("a", 143))
        self.assertEqual(gates.startup_attempts(ledger, out / "gate")[
            -1]["verdict"], "judged-incomplete")
        (out / "harness-head.txt").unlink()
        with self.assertRaisesRegex(ValueError, "records no harness"):
            gates.startup_attempts(ledger, out / "gate")
        write(out / "harness-head.txt", "0" * 40 + "\n")
        with mock.patch.object(gates, "harness_source",
                               self.real_harness_source):
            with self.assertRaisesRegex(
                    ValueError, "cannot read startup_gate.py at the "
                    "harness commit " + "0" * 40):
                gates.startup_attempts(ledger, out / "gate")
        # no gate decision, nothing to replay: the harness is not read
        void = self.run_dir("v", done=False)
        (void / "harness-head.txt").unlink()
        self.assertEqual(gates.classify(dict(
            attempt="v", output=str(void), exit=143,
            status="failed"))["kind"], "void")

    def test_the_harness_source_is_the_blob_at_the_commit_in_its_path(self):
        import subprocess
        repo = self.root / "repo"
        (repo / "sub").mkdir(parents=True)
        subprocess.run(("git", "-C", str(repo), "init", "-q"), check=True,
                       stdin=subprocess.DEVNULL)
        shas = []
        for text in (b"one\n", b"two\n"):
            (repo / "sub" / "startup_gate.py").write_bytes(text)
            for argv in (("add", "."), ("-c", "user.name=t", "-c",
                                        "user.email=t@t", "commit", "-q",
                                        "-m", "x")):
                subprocess.run(("git", "-C", str(repo)) + argv,
                               check=True, stdin=subprocess.DEVNULL)
            shas.append(subprocess.run(
                ("git", "-C", str(repo), "rev-parse", "HEAD"), check=True,
                capture_output=True, text=True).stdout.strip())
        where = repo / "sub" / "startup_gate.py"
        self.assertEqual([self.real_harness_source(c, where)
                          for c in shas], [b"one\n", b"two\n"])
        with self.assertRaisesRegex(ValueError, "cannot read"):
            self.real_harness_source("0" * 40, where)
        with self.assertRaisesRegex(ValueError, "cannot read"):
            self.real_harness_source(shas[0], repo / "startup_gate.py")

    def test_a_judged_gate_that_is_not_the_last_attempt_is_refused(self):
        one, two = self.run_dir("one"), self.run_dir("two")
        ledger = self.attempts(("one", 0), ("two", 1))
        with self.assertRaisesRegex(ValueError, "not the gate of the last"):
            gates.startup_attempts(ledger, one / "gate")

    def test_an_open_last_attempt_with_no_decision_or_a_bad_ledger_is_void(
            self):
        one = self.run_dir("one", done=False)
        with self.assertRaisesRegex(ValueError, "void"):
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
        last = self.run_dir("last", decision="pass")
        return gates.startup_attempts(
            self.attempts(*rows, ("last", 0)), last / "gate")

    def test_a_redraw_after_a_void_attempt_is_accepted(self):
        # void: the attempt left no gate decision, whatever its exit
        self.run_dir("signal", done=False)                 # exit 143
        self.run_dir("nodone", done=False)                 # exit 1
        self.run_dir("crashed", done=False)                # no decisions
        self.run_dir("killed", done=False)                 # never closed
        got = self.judged(("signal", 143), ("nodone", 1), ("crashed", 1),
                          ("killed", None))
        self.assertEqual([x["verdict"] for x in got],
                         ["void", "void", "void", "void", "judged"])

    def test_an_incomplete_earlier_attempt_blocks_only_on_a_fail(self):
        # a decided gate is not undone by a crash or a signal after it,
        # but an incomplete PASS owed the redraw and does not block it
        for name, exit_, done, decision, reasons in (
                ("f1", 1, False, "fail", ("R1 differs",)),  # non-delta
                ("f2", 130, False, "attributed", ("R3 noise",)),
                ("f3", 143, True, "blocked", ("R3 noise",))):
            self.run_dir(name, done=done, decision=decision,
                         reasons=reasons, declared=(158440, 90000))
            with self.assertRaisesRegex(ValueError, "stays judged",
                                        msg=name):
                self.judged((name, exit_))
            shutil.rmtree(self.root / name)
            shutil.rmtree(self.root / "last", ignore_errors=True)
        for name, exit_, done in (("p1", 1, False), ("p2", 143, False)):
            self.run_dir(name, done=done, decision="pass",
                         declared=(158440, 90000))
            got = self.judged((name, exit_))
            self.assertEqual((got[0]["verdict"], got[0]["complete"]),
                             ("incomplete-pass", False), name)
            shutil.rmtree(self.root / name)
            shutil.rmtree(self.root / "last", ignore_errors=True)

    def last(self, exit_, done, decision, reasons=(), declared=(
            158440, 90000)):
        out = self.run_dir("last", done=done, decision=decision,
                           reasons=reasons, declared=declared)
        return gates.startup_attempts(self.attempts(("last", exit_)),
                                      out / "gate")[-1]

    def test_an_incomplete_last_attempt_that_failed_is_the_result(self):
        for decision, reasons in (("fail", ("R1 differs",)),
                                  ("blocked", ("R3 noise",))):
            got = self.last(143, False, decision, reasons)
            self.assertEqual((got["verdict"], got["judged"],
                              got["decision"], got["complete"]),
                             ("judged-incomplete", True, decision, False))
            shutil.rmtree(self.root / "last")

    def test_an_incomplete_last_attempt_that_passed_owes_a_redraw(self):
        got = self.last(1, False, "pass")
        self.assertEqual((got["verdict"], got["problems"]),
                         ("owes-redraw", []))

    def test_an_incomplete_last_attempt_failing_on_the_deltas_is_a_fail(
            self):
        # uniform with a complete one: a fail, a redraw allowed
        got = self.last(130, False, "pass", declared=(158441, 90000))
        self.assertEqual(got["verdict"], "judged-incomplete")
        self.assertIn("load-simpLib", got["problems"][0])

    def test_an_open_last_attempt_is_classified_not_refused(self):
        got = self.last(None, False, "fail", ("R1 differs",))
        self.assertEqual((got["status"], got["verdict"], got["exit"]),
                         ("open", "judged-incomplete", None))
        shutil.rmtree(self.root / "last")
        got = self.last(None, False, "pass")
        self.assertEqual((got["status"], got["verdict"]),
                         ("open", "owes-redraw"))

    def test_an_open_earlier_attempt_is_judged_as_an_earlier_one(self):
        self.run_dir("p", done=False, decision="pass",
                     declared=(158440, 90000))
        self.run_dir("v", done=False)
        got = self.judged(("p", None), ("v", None))
        self.assertEqual([(x["status"], x["verdict"]) for x in got[:2]],
                         [("open", "incomplete-pass"),
                          ("open", "void")])
        self.run_dir("f", done=False, decision="fail",
                     reasons=("R1 differs",), declared=(158440, 90000))
        shutil.rmtree(self.root / "last")
        with self.assertRaisesRegex(ValueError, "stays judged"):
            self.judged(("f", None))

    def test_a_gate_decision_needs_a_receipt_that_matches(self):
        out = self.run_dir("g", done=False, decision="fail",
                           reasons=("R1 differs",))
        gate = out / "gate"
        self.assertEqual(gates.gate_decision(gate)["decision"], "fail")
        self.assertEqual(gates.classify(dict(
            attempt="g", output=str(out), exit=1, status="failed"))["kind"],
            "fail")
        for damage in ("receipt missing", "receipt bad", "decisions "
                       "truncated", "header edited", "row missing",
                       "decisions edited"):
            shutil.rmtree(out)
            out = self.run_dir("g", done=False, decision="fail",
                               reasons=("R1 differs",), steps=REPLAYED)
            if damage == "receipt missing":
                (gate / "receipt.json").unlink()
            elif damage == "receipt bad":
                (gate / "receipt.json").write_text("{")
            elif damage == "decisions truncated":
                text = (gate / "decisions.json").read_text()
                (gate / "decisions.json").write_text(text[:10])
            elif damage == "header edited":
                write(gate / "header.json", dict(x=1))
            elif damage == "row missing":
                doc = json.loads((gate / "receipt.json").read_text())
                doc.pop("header.json")
                write(gate / "receipt.json", doc)
            else:
                write(gate / "decisions.json", dict(decision="pass"))
            self.assertIsNone(gates.gate_decision(gate), damage)
            row = gates.classify(dict(
                attempt="g", output=str(out), exit=1, status="failed"))
            self.assertEqual(row["kind"], "void", damage)
            self.assertTrue(row["damaged"], damage)
            with self.assertRaisesRegex(ValueError, "damaged after the "
                                        "run", msg=damage):
                gates.startup_attempts(self.attempts(("g", 1)), gate)
            (out / "replay-gate.exit").unlink()    # it never got so far
            self.assertFalse(gates.classify(dict(
                attempt="g", output=str(out), exit=1,
                status="failed"))["damaged"], damage)
            with self.assertRaisesRegex(ValueError, "void", msg=damage):
                gates.startup_attempts(self.attempts(("g", 1)), gate)

    def test_a_decided_gate_that_does_not_replay_is_void(self):
        # no progress past replay-gate: it decided nothing, redraw allowed
        self.run_dir("cut", done=False, decision="fail",
                     reasons=("R1 differs",), declared=(158440, 90000),
                     replays=False)
        got = self.judged(("cut", 143))
        self.assertEqual((got[0]["verdict"], got[0]["decision"]),
                         ("void", None))
        shutil.rmtree(self.root / "cut")
        shutil.rmtree(self.root / "last")
        # the exit 1 of replay-gate itself is no progress either
        self.run_dir("bad", done=False, decision="fail",
                     reasons=("R1 differs",), declared=(158440, 90000),
                     replays=False, steps={"replay-gate.exit": "exit=1\n"})
        self.assertEqual(self.judged(("bad", 1))[0]["verdict"], "void")

    def test_progress_past_replay_gate_makes_a_non_replaying_gate_damage(
            self):
        for steps, exit_ in (
                ({"replay-gate.exit": "exit=0\n"}, 143),
                ({"check_deltas.exit": "exit=0\n"}, 143),
                ({"check_deltas.out": ""}, 143),
                ({"replay-null.err": ""}, 143),
                ({"cell-o1-19.exit": "exit=0\n"}, 143),
                ({"done": "done\n"}, 143)):
            self.run_dir("cut", done=False, decision="fail",
                         reasons=("R1 differs",), steps=steps,
                         declared=(158440, 90000), replays=False)
            with self.assertRaisesRegex(
                    ValueError, "damaged after the run", msg=steps):
                self.judged(("cut", exit_))
            shutil.rmtree(self.root / "cut")
            shutil.rmtree(self.root / "last", ignore_errors=True)

    def test_a_signal_after_a_decided_replayable_gate_keeps_the_decision(
            self):
        # killed during gate-null: no replay-gate.exit, no later file
        self.run_dir("cut", done=False, decision="fail",
                     reasons=("R1 differs",), declared=(158440, 90000))
        with self.assertRaisesRegex(ValueError, "stays judged"):
            self.judged(("cut", 143))
        # deleting replay-gate.exit of a decided attempt changes nothing
        for steps in ({}, REPLAYED):
            shutil.rmtree(self.root / "cut", ignore_errors=True)
            shutil.rmtree(self.root / "last", ignore_errors=True)
            out = self.run_dir("cut", done=False, decision="fail",
                               reasons=("R1 differs",), steps=steps,
                               declared=(158440, 90000))
            (out / "replay-gate.exit").unlink(missing_ok=True)
            self.assertEqual(gates.classify(dict(
                attempt="cut", output=str(out), exit=143,
                status="failed"))["kind"], "fail")
            with self.assertRaisesRegex(ValueError, "stays judged"):
                self.judged(("cut", 143))

    def test_a_damaged_earlier_attempt_is_refused_not_redrawn(self):
        for done, exit_ in ((True, 0), (True, 2), (False, 143)):
            for damage in ("receipt", "row", "file", "extra row"):
                run = self.run_dir("d", done=done, decision="pass",
                                   declared=(158440, 90000),
                                   steps=REPLAYED)
                gate = run / "gate"
                if damage == "receipt":
                    (gate / "receipt.json").write_text("not json")
                elif damage == "row":
                    doc = json.loads((gate / "receipt.json").read_text())
                    doc["header.json"] = "0" * 64
                    write(gate / "receipt.json", doc)
                elif damage == "file":
                    (gate / "decisions.json").unlink()
                else:           # a file the receipt lists, now missing
                    doc = json.loads((gate / "receipt.json").read_text())
                    doc["RESULTS.md"] = "0" * 64
                    write(gate / "receipt.json", doc)
                with self.assertRaisesRegex(
                        ValueError, "damaged after the run",
                        msg=(done, damage)):
                    self.judged(("d", exit_))
                shutil.rmtree(run)
                shutil.rmtree(self.root / "last", ignore_errors=True)

    def test_a_damaged_last_attempt_is_refused(self):
        for done, exit_ in ((True, 0), (False, 143)):
            out = self.run_dir("last", done=done, decision="pass",
                               declared=(158440, 90000), steps=REPLAYED)
            (out / "gate" / "receipt.json").unlink()
            with self.assertRaisesRegex(ValueError, "damaged after the "
                                        "run", msg=done):
                gates.startup_attempts(self.attempts(("last", exit_)),
                                       out / "gate")
            shutil.rmtree(out)

    def test_every_listed_file_of_the_receipt_must_match(self):
        out = self.run_dir("g", done=False, decision="pass")
        gate = out / "gate"
        write(gate / "RESULTS.md", "text\n")
        doc = json.loads((gate / "receipt.json").read_text())
        doc["RESULTS.md"] = hashlib.sha256(
            (gate / "RESULTS.md").read_bytes()).hexdigest()
        write(gate / "receipt.json", doc)
        self.assertEqual(gates.gate_decision(gate)["decision"], "pass")
        write(gate / "RESULTS.md", "edited\n")
        self.assertIsNone(gates.gate_decision(gate))

    def test_owing_a_redraw_makes_the_gate_record_incomplete(self):
        row = self.last(143, False, "pass", declared=(158441, 90000))
        record = gates.owe_redraw(gates.startup_gate(
            dict(record_sha256="x"), dict(decision="pass"),
            dict(decision="pass"), row["problems"]), row)
        self.assertEqual((record["failed"], record["owed"]),
                         ([], ["redraw"]))
        self.assertIn("incomplete", record["missing"][0])
        self.assertEqual(record["source"], "inconclusive")

    def test_a_redraw_after_an_incomplete_pass_is_accepted(self):
        self.run_dir("cut", done=False, decision="pass",
                     declared=(158440, 90000))
        got = self.judged(("cut", 143))
        self.assertEqual([x["verdict"] for x in got],
                         ["incomplete-pass", "judged"])

    def test_a_redraw_after_a_complete_pass_is_refused(self):
        self.run_dir("done", decision="pass", declared=(158440, 90000))
        with self.assertRaisesRegex(ValueError, "stays judged"):
            self.judged(("done", 0))

    def test_a_redraw_after_a_non_delta_fail_is_refused(self):
        self.run_dir("bad", decision="fail", reasons=("R1 differs",),
                     declared=(158441, 90000))
        with self.assertRaisesRegex(ValueError, "stays judged"):
            self.judged(("bad", 2))

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
            shutil.rmtree(self.root / "bad")
            shutil.rmtree(self.root / "last", ignore_errors=True)


class ReplayValidity(Ledgers):
    """A gate decision counts iff its receipt rows match and its archive
    replays (design decision 28): REAL archives, written by
    `startup_gate.write_archive` and replayed by `startup_gate.replay`."""
    def setUp(self):
        super().setUp()
        import startup_gate as sg
        self.sg = sg
        patch = mock.patch.object(sg, "PAIRS", tsg.TEST_PAIRS)
        patch.start()
        self.addCleanup(patch.stop)
        # the attempt's own module, loaded from its source, has the
        # archives' pair count too
        self.frozen = self.frozen.replace(b"PAIRS = 10  #", b"PAIRS = 2  #")
        self.assertIn(b"PAIRS = 2  #", self.frozen)

    def run_dir(self, name, fail=False, done=False, steps=None):
        """An attempt whose gate is a real archive: attributed, or with
        `fail` failed (an undeclared file carries words), sealed to the
        attempt's own record."""
        path = self.root / name
        write(path / "harness-head.txt", HARNESS + "\n")
        record = write(path / "not-client-visible.md", "record\n")
        records = tsg.world(delta=dict(tsg.DELTA, **(
            {"Other.sml": 3} if fail else {})))
        (path / "gate").mkdir()
        tsg.ArchiveTest().archive(path / "gate", records,
                                  self.sg.sha_file(record))
        if done:
            write(path / "done", "done\n")
        for step, text in (steps or {}).items():
            write(path / step, text)
        return path

    def row(self, path, exit_=143):
        return dict(attempt=path.name, output=str(path), exit=exit_,
                    status="failed")

    def forge(self, path):
        """The gate's decision edited and the receipt rewritten to match:
        every row matches, and the archive no longer replays."""
        gate = path / "gate"
        text = (gate / "decisions.json").read_text()
        (gate / "decisions.json").write_text(
            text.replace('"attributed"', '"pass"').replace(
                '"fail"', '"pass"'))
        write(gate / "receipt.json", {
            n: self.sg.sha_file(gate / n) for n in json.loads(
                (gate / "receipt.json").read_text())})
        self.assertIsNotNone(gates.gate_decision(gate))

    def test_a_replayable_gate_is_judged_by_its_decision(self):
        for fail, kind in ((False, "pass"), (True, "fail")):
            out = self.run_dir("g%d" % fail, fail=fail, done=True)
            got = gates.classify(self.row(out, 0))
            self.assertEqual((got["kind"], got["damaged"]), (kind, ""))
            self.assertEqual(got["decision"],
                             "fail" if fail else "attributed")

    def test_a_signal_after_a_decided_replayable_gate_keeps_it(self):
        # killed during gate-null: no replay-gate.exit, no later file
        out = self.run_dir("cut", fail=True)
        got = gates.classify(self.row(out))
        self.assertEqual((got["kind"], got["damaged"]), ("fail", ""))
        with self.assertRaisesRegex(ValueError, "stays judged"):
            gates.startup_attempts(self.attempts(("cut", 143), (
                "last", 0)), self.run_dir("last", done=True) / "gate")
        last = gates.startup_attempts(self.attempts(("cut", 143)),
                                      out / "gate")[-1]
        self.assertEqual((last["verdict"], last["decision"]),
                         ("judged-incomplete", "fail"))
        # deleting replay-gate.exit (or writing it) changes nothing
        for steps in ({}, {"replay-gate.exit": "exit=0\n"}):
            out = self.run_dir("more", fail=True, steps=steps)
            (out / "replay-gate.exit").unlink(missing_ok=True)
            self.assertEqual(gates.classify(self.row(out))["kind"], "fail")
            shutil.rmtree(out)

    def test_a_decided_archive_that_does_not_replay_is_void(self):
        out = self.run_dir("forged")
        self.forge(out)
        got = gates.classify(self.row(out))
        self.assertEqual((got["kind"], got["damaged"]), ("void", ""))
        got = gates.startup_attempts(self.attempts(
            ("forged", 143), ("last", 0)),
            self.run_dir("last", done=True) / "gate")
        self.assertEqual([x["verdict"] for x in got], ["void", "judged"])
        with self.assertRaisesRegex(ValueError, "is void"):
            gates.startup_attempts(self.attempts(("forged", 143)),
                                   out / "gate")

    def test_a_record_that_is_not_the_seal_does_not_replay(self):
        out = self.run_dir("g")
        write(out / "not-client-visible.md", "edited\n")
        self.assertEqual(gates.classify(self.row(out))["kind"], "void")
        (out / "not-client-visible.md").unlink()
        self.assertEqual(gates.classify(self.row(out))["kind"], "void")

    def test_progress_past_replay_gate_makes_it_damage(self):
        for steps, exit_, done in (
                ({"replay-gate.exit": "exit=0\n"}, 143, False),
                ({"check_deltas.exit": "exit=2\n"}, 143, False),
                ({"replay-null.out": ""}, 143, False),
                ({"cell-o1-19.exit": "exit=0\n"}, 130, False),
                ({}, 143, True), ({}, 0, True)):
            out = self.run_dir("p", steps=steps, done=done)
            self.forge(out)
            got = gates.classify(self.row(out, exit_))
            self.assertEqual(got["kind"], "void", steps)
            self.assertIn("damaged after the run", got["damaged"], steps)
            with self.assertRaisesRegex(ValueError, "damaged after",
                                        msg=steps):
                gates.startup_attempts(self.attempts(("p", exit_)),
                                       out / "gate")
            with self.assertRaisesRegex(ValueError, "damaged after",
                                        msg=steps):
                gates.startup_attempts(self.attempts(
                    ("p", exit_), ("last", 0)),
                    self.run_dir("last", done=True) / "gate")
            shutil.rmtree(out)
            shutil.rmtree(self.root / "last", ignore_errors=True)

    def test_the_replay_is_the_attempts_own_module_from_git(self):
        import subprocess
        import sys
        head = subprocess.run(
            ("git", "-C", str(Path(gates.__file__).parent), "rev-parse",
             "HEAD"), check=True, capture_output=True, text=True,
            stdin=subprocess.DEVNULL).stdout.strip()
        out = self.run_dir("g", fail=True)
        write(out / "harness-head.txt", head + "\n")
        row = self.row(out)
        with mock.patch.object(gates, "harness_source",
                               self.real_harness_source):
            module = gates.attempt_startup_gate(row)
            self.assertIs(sys.modules["startup_gate"], self.sg)
            self.assertIsNot(module, self.sg)
            self.assertNotIn(module.__name__, sys.modules)
            # real blob, real replay of a real archive (its pair count is
            # the archive's)
            with mock.patch.object(module, "PAIRS", tsg.TEST_PAIRS):
                self.assertEqual(gates.replays(
                    out / "gate", out / "not-client-visible.md",
                    module=module), (True, ""))

    def test_the_attempts_version_of_the_replay_is_the_one_used(self):
        out = self.run_dir("g", fail=True)
        self.assertEqual(gates.classify(self.row(out))["kind"], "fail")
        # an attempt whose harness had another `replay`
        self.frozen = b"def replay(args):\n    return 7\n"
        got = gates.classify(self.row(out))
        self.assertEqual(got["kind"], "void")
        self.assertIn("returned 7", got["replay"])
        # a null is replayed by it too
        self.assertEqual(gates.replays(
            out / "gate", out / "not-client-visible.md",
            module=gates.attempt_startup_gate(self.row(out))),
            (False, "the replay returned 7"))

    def test_a_replay_that_is_not_run_gives_no_decision(self):
        out = self.run_dir("g")
        gate, record = out / "gate", out / "not-client-visible.md"
        with mock.patch.object(self.sg, "replay", side_effect=KeyError):
            ok, reason = gates.replays(gate, record)
        self.assertFalse(ok)
        self.assertIn("KeyError", reason)
        self.assertEqual(gates.replays(gate, record), (True, ""))
        # the sealed branch: the record is needed, and is the seal
        ok, reason = gates.replays(gate)
        self.assertFalse(ok)
        self.assertIn("--record", reason)
        write(record, "edited\n")
        ok, reason = gates.replays(gate, record)
        self.assertFalse(ok)
        self.assertIn("differs from its seal", reason)
        self.assertFalse(gates.replays(out / "nowhere")[0])
        # a gate sealed to no record gives no decision, and a null is
        # sealed to none
        header = json.loads((gate / "header.json").read_text())
        self.assertFalse(gates.replays(gate, record, null=True)[0])
        header["record_sha256"] = None
        write(gate / "header.json", header)
        ok, reason = gates.replays(gate, record)
        self.assertFalse(ok)
        self.assertIn("no record", reason)

    def test_the_reason_is_in_the_messages_and_the_row(self):
        out = self.run_dir("forged")
        self.forge(out)
        got = gates.classify(self.row(out))
        self.assertIn("stored decisions differ", got["replay"])
        with self.assertRaisesRegex(ValueError, "stored decisions differ"):
            gates.startup_attempts(self.attempts(("forged", 143)),
                                   out / "gate")
        out = self.run_dir("p", steps={"replay-gate.exit": "exit=0\n"})
        self.forge(out)
        with self.assertRaisesRegex(ValueError, "stored decisions differ"):
            gates.startup_attempts(self.attempts(("p", 143)), out / "gate")
        rows = gates.startup_attempts(self.attempts(
            ("forged", 143), ("last", 0)),
            self.run_dir("last", done=True) / "gate")
        self.assertIn("stored decisions differ", rows[0]["replay"])


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


class StartupPath(Ledgers):
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
        super().setUp()
        self.cand = "c" * 40
        self.ev = self.root / "attempt"
        (self.archive, self.record, self.side,
         self.header) = archive_fixture(
             self.ev, prefix="Baseline: develop %s\n%s\n" % (
                 a.BASE, self.cand))
        self.unreplayable, self.replayed = set(), []
        for patch in (
                mock.patch.object(gates, "replays", self.replays),
                mock.patch.object(gates, "read_loading", lambda out, gate,
                                  lineage: (dict(stage="second"), "pass")),
                mock.patch.object(gates, "check_one_audit",
                                  lambda reports: {"sha256": "x"}),
                mock.patch.object(gates, "replay_loading"),
                mock.patch.object(gates, "replay_startup")):
            patch.start()
            self.addCleanup(patch.stop)

    def replays(self, out, record=None, null=False, module=None):
        """Stands in for `gates.replays` over the fake archives here."""
        self.replayed.append((Path(out).name, null, module))
        if str(Path(out).resolve()) in self.unreplayable:
            return False, "marked as not replaying"
        return True, ""

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
        seal_gate(directory)

    def make(self, exit_="auto", total=(158440, 90000), done=True):
        """The attempt: closed with `exit_` (by default 0 with `done`, 143
        without), open when None."""
        self.ev.mkdir(exist_ok=True)
        write(self.ev / "harness-head.txt", HARNESS + "\n")
        if exit_ == "auto":
            exit_ = 0 if done else 143
        self.archive_of(self.ev / "gate", False, total)
        self.archive_of(self.ev / "gate-null", True)
        if done:
            write(self.ev / "done", "done\n")
        write(self.ev / "inputs.txt", "A=b\nDECLARED_DELTAS_SHA256=%s\n"
              % hashlib.sha256(self.side.read_bytes()).hexdigest())
        ledger = write(self.root / "attempts.jsonl", "".join(
            json.dumps(x) + "\n" for x in [dict(
                event="open", attempt="attempt", output=str(self.ev))] + (
                    [] if exit_ is None else [dict(
                        event="close", attempt="attempt",
                        output=str(self.ev), exit=exit_)])))
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
            "record", "declared", "ledger", "done", "attempt-inputs"})
        self.assertEqual(inputs[gates.STARTUP]["attempt-inputs"],
                         a.seal(self.ev / "inputs.txt"))
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

    def test_an_incomplete_attempt_with_a_decision_is_judged_by_it(self):
        found, inputs, _, extra = self.read(self.make(done=False))
        record = found[gates.STARTUP]      # a passing gate owes a redraw
        self.assertEqual((record["source"], record["owed"]),
                         ("inconclusive", ["redraw"]))
        self.assertEqual(inputs[gates.STARTUP]["done"], "absent")
        self.assertEqual(extra["startup_attempts"][-1]["verdict"],
                         "owes-redraw")
        found, _, _, extra = self.read(self.make(exit_=143, done=False))
        self.assertEqual(found[gates.STARTUP]["owed"], ["redraw"])

    def test_an_incomplete_failed_attempt_is_a_fail(self):
        args = self.make(done=False)
        write(self.ev / "gate" / "decisions.json", dict(
            decision="fail", reasons=["R1 differs"], R2=r2()))
        seal_gate(self.ev / "gate")
        args.startup_null = None
        found, _, _, extra = self.read(args)
        self.assertEqual(found[gates.STARTUP]["source"], "fail")
        self.assertEqual(extra["startup_attempts"][-1]["verdict"],
                         "judged-incomplete")

    def test_a_complete_attempt_needs_its_null_control(self):
        args = self.make()
        args.startup_null = None
        with self.assertRaisesRegex(ValueError, "needs --startup-null"):
            self.read(args)

    def test_an_incomplete_failure_without_a_null_is_a_fail(self):
        args = self.make(done=False, exit_=143)
        shutil.rmtree(self.ev / "gate-null")
        write(self.ev / "gate" / "decisions.json", dict(
            decision="fail", reasons=["R1 differs"], R2=r2()))
        seal_gate(self.ev / "gate")
        for given in (None, self.ev / "gate-null"):
            args.startup_null = given
            if given is not None:
                with self.assertRaisesRegex(ValueError,
                                            "complete attempt only"):
                    self.read(args)
                continue
            found, inputs, late, _ = self.read(args)
            self.assertEqual(found[gates.STARTUP]["source"], "fail")
            self.assertEqual(inputs[gates.STARTUP]["null-header"],
                             d.NULL_NA)
            self.assertEqual(inputs[gates.STARTUP]["null-decisions"],
                             d.NULL_NA)
            with mock.patch.object(gates, "replay_startup") as replay:
                late[0][1]()
            self.assertEqual(replay.call_count, 1)    # the gate only

    def test_an_incomplete_pass_without_a_null_owes_a_redraw(self):
        args = self.make(done=False)
        shutil.rmtree(self.ev / "gate-null")
        args.startup_null = None
        found, _, _, extra = self.read(args)
        self.assertEqual((found[gates.STARTUP]["source"],
                          found[gates.STARTUP]["owed"]),
                         ("inconclusive", ["redraw"]))

    def test_an_incomplete_attempt_reads_a_complete_null_archive(self):
        args = self.make(done=False)
        args.startup_null = None          # found as the attempt's gate-null
        found, inputs, late, _ = self.read(args)
        self.assertNotEqual(inputs[gates.STARTUP]["null-header"],
                            d.NO_NULL)
        with mock.patch.object(gates, "replay_startup") as replay:
            late[0][1]()
        self.assertEqual(replay.call_count, 2)
        # an archive with no receipt is not a complete one
        (self.ev / "gate-null" / "receipt.json").unlink()
        found, inputs, _, _ = self.read(args)
        self.assertEqual(inputs[gates.STARTUP]["null-header"], d.NO_NULL)

    def test_an_explicit_null_of_an_incomplete_attempt_must_be_its_own(
            self):
        args = self.make(done=False)         # owes a redraw
        found, _, _, _ = self.read(args)     # its own complete gate-null
        self.assertEqual(found[gates.STARTUP]["owed"], ["redraw"])
        (self.ev / "gate-null" / "receipt.json").unlink()
        with self.assertRaisesRegex(ValueError, "omit the flag"):
            self.read(args)                  # no receipt: not complete
        args.startup_null = None             # found by itself: absent
        found, inputs, _, _ = self.read(args)
        self.assertEqual(inputs[gates.STARTUP]["null-header"], d.NO_NULL)
        other = self.root / "other"
        self.archive_of(other / "gate-null", True)
        args.startup_null = other / "gate-null"
        with self.assertRaisesRegex(ValueError, "omit the flag"):
            self.read(args)                  # a complete one, not its own

    def test_the_null_of_a_failed_incomplete_attempt_is_never_read(self):
        args = self.make(done=False, exit_=143)
        write(self.ev / "gate" / "decisions.json", dict(
            decision="fail", reasons=["R1 differs"], R2=r2()))
        seal_gate(self.ev / "gate")
        (self.ev / "gate-null" / "header.json").write_text("{")  # damaged
        args.startup_null = None
        found, inputs, late, extra = self.read(args)
        self.assertEqual(found[gates.STARTUP]["source"], "fail")
        self.assertEqual(inputs[gates.STARTUP]["null-header"], d.NULL_NA)
        self.assertEqual(extra["startup_attempts"][-1]["verdict"],
                         "judged-incomplete")
        with mock.patch.object(gates, "replay_startup") as replay:
            late[0][1]()
        self.assertEqual(replay.call_count, 1)    # the gate only

    def test_a_failed_incomplete_attempt_has_a_failed_status(self):
        args = self.make(done=False)
        write(self.ev / "gate" / "decisions.json", dict(
            decision="pass", reasons=["R3 noise"], R2=r2()))
        seal_gate(self.ev / "gate")
        args.startup_null = None
        with self.assertRaisesRegex(ValueError, "not fail or inconclusive"):
            self.read(args)       # reasons make it a fail, `pass` is not
        write(self.ev / "gate" / "decisions.json", dict(
            decision="blocked", blockers=["R3 noise"], R2=r2()))
        seal_gate(self.ev / "gate")
        found, _, _, _ = self.read(args)
        self.assertEqual(found[gates.STARTUP]["source"], "inconclusive")

    def test_a_decided_gate_that_does_not_replay_is_void(self):
        args = self.make(done=False, exit_=143)
        write(self.ev / "gate" / "decisions.json", dict(
            decision="fail", reasons=["R1 differs"], R2=r2()))
        seal_gate(self.ev / "gate")
        self.unreplayable.add(str(self.ev / "gate"))
        with self.assertRaisesRegex(ValueError, "void"):
            self.read(args)

    def test_a_null_is_replayed_as_a_null_and_a_gate_as_a_gate(self):
        args = self.make(done=False)
        args.startup_null = None
        self.read(args)
        module = object()
        self.assertEqual(sorted({(n, null) for n, null, _ in self.replayed}),
                         [("gate", False), ("gate-null", True)])
        # the late replays, and the null's, use the attempt's own module
        with mock.patch.object(gates, "attempt_startup_gate",
                               lambda row: module):
            self.replayed.clear()
            _, _, late, _ = self.read(args)
            with mock.patch.object(gates, "replay_startup") as replay:
                late[0][1]()
        self.assertEqual({m for _, _, m in self.replayed}, {module})
        self.assertEqual([c.args[-1] for c in replay.call_args_list],
                         [module, module])

    def test_the_replay_reason_is_in_the_attempt_line(self):
        record = dict(timing_attempts={}, identity_unaccounted={},
                      cells={}, task32={}, task33={}, gates={},
                      identity_grid={}, allocation_case={},
                      timing_grid={}, retained_slope={},
                      startup_attempts=[dict(
                          attempt="a", status="failed", judged=False,
                          verdict="void", decision=None, problems=[],
                          replay="the replay returned 7")])
        self.assertIn("replay: the replay returned 7", d.lines(record)[0])

    def test_the_null_that_does_not_replay_is_recorded_absent(self):
        # an attempt owing a redraw: its null cannot change the verdict
        args = self.make(done=False)
        args.startup_null = None
        self.unreplayable.add(str(self.ev / "gate-null"))
        found, inputs, late, _ = self.read(args)
        self.assertEqual(inputs[gates.STARTUP]["null-header"], d.NO_NULL)
        self.assertEqual(found[gates.STARTUP]["owed"], ["redraw"])
        with mock.patch.object(gates, "replay_startup") as replay:
            late[0][1]()
        self.assertEqual(replay.call_count, 1)        # the gate only
        # an explicit flag naming that archive is refused, not absent
        args.startup_null = self.ev / "gate-null"
        with self.assertRaisesRegex(ValueError, "does not replay"):
            self.read(args)

    def test_the_null_of_a_complete_attempt_must_replay(self):
        args = self.make()
        with mock.patch.object(gates, "replay_startup") as replay:
            _, _, late, _ = self.read(args)
            late[0][1]()
        self.assertEqual(replay.call_count, 2)
        def replay_one(out, record, module=None):
            if Path(out).name == "gate-null":
                raise ValueError("did not replay")
        with mock.patch.object(gates, "replay_startup", replay_one):
            with self.assertRaisesRegex(ValueError, "did not replay"):
                late[0][1]()

    def test_an_open_last_attempt_is_read(self):
        args = self.make(done=False, exit_=None)
        found, inputs, _, extra = self.read(args)
        self.assertEqual((extra["startup_attempts"][-1]["status"],
                          extra["startup_attempts"][-1]["verdict"]),
                         ("open", "owes-redraw"))
        self.assertEqual(found[gates.STARTUP]["owed"], ["redraw"])
        self.assertEqual(inputs[gates.STARTUP]["done"], "absent")

    def test_the_judged_gate_and_sidecar_are_the_last_attempts_own(self):
        args = self.make()
        other = self.root / "other"
        self.archive_of(other / "gate", False)
        args.startup_gate = other / "gate"
        with self.assertRaisesRegex(ValueError, "not the gate of the "
                                    "last"):
            self.read(args)
        args = self.make()
        elsewhere = self.root / "elsewhere"
        elsewhere.mkdir()
        (elsewhere / "declared-deltas.json").write_bytes(
            self.side.read_bytes())
        args.startup_declared = elsewhere / "declared-deltas.json"
        with self.assertRaisesRegex(ValueError, "not the declared-deltas"):
            self.read(args)

    def test_the_judged_gate_must_be_exactly_the_gate_of_the_last_attempt(
            self):
        # a copy of the archive under the last attempt, not named `gate`
        args = self.make()
        shutil.copytree(self.ev / "gate", self.ev / "gate2")
        args.startup_gate = self.ev / "gate2"
        with self.assertRaisesRegex(ValueError, "not the gate of the "
                                    "last"):
            self.read(args)

    def test_an_explicit_null_of_another_attempt_is_refused_by_that_alone(
            self):
        # the attempt's own gate-null is complete (and would be used)
        args = self.make(done=False)
        args.startup_null = None
        found, inputs, _, _ = self.read(args)
        self.assertNotEqual(inputs[gates.STARTUP]["null-header"],
                            d.NO_NULL)
        other = self.root / "other"
        self.archive_of(other / "gate-null", True)
        self.assertTrue(gates.archive_complete(other / "gate-null"))
        args.startup_null = other / "gate-null"
        with self.assertRaisesRegex(ValueError, "omit the flag"):
            self.read(args)

    def test_an_incomplete_attempt_with_no_decision_is_refused(self):
        args = self.make(done=False)
        (self.ev / "gate" / "decisions.json").unlink()
        with self.assertRaisesRegex(ValueError, "decisions"):
            self.read(args)

    def test_the_attempt_inputs_must_exist(self):
        args = self.make()
        (self.ev / "inputs.txt").unlink()
        with self.assertRaisesRegex(ValueError, "no sealed inputs.txt"):
            self.read(args)

    def test_the_gate_and_its_null_control_must_be_of_one_attempt(self):
        args = self.make()
        other = self.root / "other"
        other.mkdir()
        self.archive_of(other / "gate-null", True)
        args.startup_null = other / "gate-null"
        with self.assertRaisesRegex(ValueError, "not the gate-null of the "
                                    "judged attempt"):
            self.read(args)
        # a copy of its own null under another name is refused too
        args = self.make()
        shutil.copytree(self.ev / "gate-null", self.ev / "gate-null.ok")
        args.startup_null = self.ev / "gate-null.ok"
        with self.assertRaisesRegex(ValueError, "not the gate-null of the "
                                    "judged attempt"):
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
