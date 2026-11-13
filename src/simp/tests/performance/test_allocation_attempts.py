#!/usr/bin/env python3
"""The attempts ledger of the TASK37 allocation tasks (R-1). Synthetic
ledgers and outputs only: no runtime, toolchain or HOL process."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import acceptance as a
import allocation_attempts as at
import allocation_matrix as m
import allocation_schema as sc
import test_task37_allocation as t37
import timing_grid as tg

CAND = "c" * 40
TASK = "task37-matrix"


def namespace(repo, output, resume=False, task=TASK, only=None,
              pairs=None):
    import argparse
    return argparse.Namespace(task=task, repo=repo, output=output,
                              resume=resume, only=only, pairs=pairs)


class Fixture(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name).resolve() / "repo"
        self.repo.mkdir()
        counts = Path(self.tmp.name) / "counts.json"
        counts.write_text("{}")
        for name in at.TASKS:
            task = m.TASKS[name]
            self.addCleanup(setattr, task, "iterations", task.iterations)
            task.iterations = counts
        for patch in (
                mock.patch.object(at.Attempt, "check_ignored"),
                mock.patch.object(at.a, "git", return_value=CAND)):
            patch.start()
            self.addCleanup(patch.stop)

    def out(self, name="o1", cells=(), inventory=None):
        path = Path(self.tmp.name) / name
        path.mkdir()
        for cell in cells:
            (path / cell).write_bytes(b"x")
        if inventory is not None:
            (path / "inventory.json").write_text(json.dumps(inventory))
        return path

    def run_with(self, output, effect, resume=False, task=TASK, **more):
        def grid(args, task_, started):
            if started is not None:
                started(dict(candidate=CAND))
            if isinstance(effect, BaseException):
                raise effect
            return effect
        with mock.patch.object(m, "run_grid", grid):
            return m.run(namespace(self.repo, output, resume, task,
                                   **more))

    def ledger(self):
        return at.ledger_path(self.repo, TASK)

    def lines(self):
        return [json.loads(x) for x in
                self.ledger().read_text().splitlines()]


class Recording(Fixture):
    def test_the_tasks_that_record_are_the_task37_tasks(self):
        self.assertEqual(
            sorted(n for n in m.TASKS if m.TASKS[n].ledger),
            sorted(at.TASKS))
        for name in ("task29b", "task30", "task31"):
            self.assertFalse(m.TASKS[name].ledger, name)

    def test_a_legacy_run_writes_no_ledger(self):
        out = self.out()
        with mock.patch.object(m, "run_grid", return_value=0) as grid:
            self.assertEqual(m.run(namespace(self.repo, out,
                                             task="task30")), 0)
        self.assertEqual(grid.call_args[0][2], None)
        self.assertFalse((self.repo / ".agent-files").exists())

    def test_a_run_opens_and_closes_with_its_decisions_status(self):
        for code, status in ((0, "pass"), (1, "fail"), (2, "inconclusive")):
            ledger = self.ledger()
            ledger.unlink(missing_ok=True)
            out = self.out("o%d" % code)
            self.assertEqual(self.run_with(out, code), code)
            first, last = self.lines()
            self.assertEqual((first["event"], last["event"],
                              last["status"]), ("open", "close", status))
            for line in (first, last):
                self.assertEqual(
                    (line["table"], line["stage"], line["candidate"],
                     line["output"], line["checkout"],
                     line["attempt"]),
                    (TASK, "first", CAND, str(out), str(self.repo),
                     at.attempt_id(out)))
                self.assertEqual(
                    line["counts_file"],
                    "counts.json")
                self.assertEqual(len(line["counts"]), 64)
            tg.Ledger(ledger)  # the chain verifies

    def test_a_run_that_raises_closes_failed_and_reraises(self):
        out = self.out()
        with self.assertRaises(sc.InvalidAllocation):
            self.run_with(out, sc.InvalidAllocation("boom"))
        first, last = self.lines()
        self.assertEqual((last["status"], first["event"]),
                         ("failed", "open"))
        self.assertIn("boom", last["failure"])

    def test_a_signal_closes_the_attempt_too(self):
        with self.assertRaises(KeyboardInterrupt):
            self.run_with(self.out(), KeyboardInterrupt())
        self.assertEqual(self.lines()[-1]["status"], "failed")

    def test_a_refusal_before_the_opening_leaves_no_line(self):
        def grid(args, task, started):
            raise sc.InvalidAllocation("refused")
        with mock.patch.object(m, "run_grid", grid), \
                self.assertRaises(sc.InvalidAllocation):
            m.run(namespace(self.repo, self.out()))
        self.assertFalse(self.ledger().exists())

    def test_a_resumption_is_a_resume_line_of_the_same_attempt(self):
        out = self.out()
        with self.assertRaises(KeyboardInterrupt):
            self.run_with(out, KeyboardInterrupt())
        self.run_with(out, 0, resume=True)
        events = [(x["event"], x.get("status")) for x in self.lines()]
        self.assertEqual(events, [("open", None), ("close", "failed"),
                                  ("resume", None), ("close", "pass")])
        self.assertEqual(len({x["attempt"] for x in self.lines()}), 1)

    def test_an_output_is_one_attempt_and_is_not_opened_twice(self):
        out = self.out()
        with self.assertRaises(sc.InvalidAllocation):
            self.run_with(out, sc.InvalidAllocation("measured"))
        before = self.ledger().read_text()
        for effect in (0, sc.InvalidAllocation("again")):
            with self.assertRaises(sc.InvalidAllocation) as caught:
                self.run_with(out, effect)
            self.assertIn("use a new output path", str(caught.exception))
        self.assertEqual(self.ledger().read_text(), before)
        # a new output is a new attempt; the earlier failure stays
        other = self.out("o2")
        self.assertEqual(self.run_with(other, 0), 0)
        self.assertEqual(len({x["attempt"] for x in self.lines()}), 2)

    def test_a_refused_open_writes_no_close(self):
        out = self.out()
        with mock.patch.object(at.Attempt, "line",
                               side_effect=OSError("disk")), \
                self.assertRaises(OSError):
            self.run_with(out, 0)
        self.assertFalse(self.ledger().exists())

    def test_only_and_smoke_runs_are_information_runs(self):
        for name, more in (("only", dict(only=["a-1"])),
                           ("smoke", dict(pairs=2))):
            with self.subTest(name):
                self.ledger().unlink(missing_ok=True)
                out = self.out(name)
                self.assertEqual(self.run_with(out, 0, **more), 0)
                first, last = self.lines()
                self.assertEqual((first["event"], last["event"],
                                  last["success"], last["status"]),
                                 ("info", "info-end", True, "pass"))
                self.assertEqual(first["attempt"], at.attempt_id(out))
                tg.Ledger(self.ledger())
                self.assertEqual(tg.Ledger(self.ledger()).attempts(TASK),
                                 {})
                self.assertEqual(at.attempts_of(TASK, self.ledger()), [])
        # a run with the task's pairs is judged
        out = self.out("full")
        self.run_with(out, 0, pairs=m.TASKS[TASK].pairs)
        self.assertEqual(self.lines()[-2]["event"], "open")

    def test_a_failed_information_run_is_not_an_attempt(self):
        out = self.out()
        with self.assertRaises(sc.InvalidAllocation):
            self.run_with(out, sc.InvalidAllocation("boom"), only=["a-1"])
        first, last = self.lines()
        self.assertEqual((first["event"], last["event"], last["success"]),
                         ("info", "info-end", False))
        self.assertEqual(at.attempts_of(TASK, self.ledger()), [])

    def test_judged_and_information_runs_never_share_an_output(self):
        info, judged = self.out("i"), self.out("j")
        self.run_with(info, 0, only=["a-1"])
        self.run_with(judged, 0)
        for out, more in ((info, {}), (judged, dict(only=["a-1"]))):
            with self.assertRaises(sc.InvalidAllocation):
                self.run_with(out, 0, **more)

    def test_the_ledger_of_a_task_is_its_own(self):
        self.assertEqual(
            at.ledger_path(self.repo, "task37-client"),
            self.repo / ".agent-files/evidence/task37-client/"
            "attempts.jsonl")
        for task in ("task30", "task31", "x"):
            with self.assertRaises(sc.InvalidAllocation):
                at.ledger_path(self.repo, task)

    def test_an_unwritable_close_is_noted_and_leaves_the_attempt_open(self):
        out = self.out()
        real = tg.ledger_append

        def append(path, **record):
            if record["event"] == "close":
                raise OSError("disk")
            return real(path, **record)
        with mock.patch.object(tg, "ledger_append", append):
            self.assertEqual(self.run_with(out, 0), 0)
        self.assertEqual([x["event"] for x in self.lines()], ["open"])
        row = tg.Ledger(self.ledger()).attempts(TASK)
        self.assertEqual(list(row.values())[0]["status"], "interrupted")


class Attempts(Fixture):
    def attempt(self, out, *events, resume=False):
        """Append `events` ((event, status)) for the output `out`."""
        for event, status in events:
            more = dict(status=status) if status else {}
            tg.ledger_append(
                self.ledger(), event=event, stage="first", table=TASK,
                attempt=at.attempt_id(out), candidate=CAND,
                counts_file="c.json", counts="0" * 64, output=str(out),
                checkout=str(self.repo), **more) if (
                    self.ledger().parent.mkdir(parents=True,
                                               exist_ok=True) or True) \
                else None
        return at.attempt_id(out)

    def test_a_failed_attempt_with_no_cell_is_void(self):
        out = self.out(inventory=dict(runs=[]))
        key = self.attempt(out, ("open", None), ("close", "failed"))
        found = at.attempts_of(TASK, self.ledger())
        self.assertEqual(
            found, [dict(attempt=key, status="failed", output=str(out),
                         judged=False, void=True)])

    def test_the_judged_attempt_stands_beside_the_void_one(self):
        void = self.out("v")
        done = self.out("d", cells=["x-1.json.xz"])
        k1 = self.attempt(void, ("open", None), ("close", "failed"))
        k2 = self.attempt(done, ("open", None), ("close", "pass"))
        found = at.attempts_of(TASK, self.ledger(), {k2: done})
        self.assertEqual([(e["attempt"], e["judged"], e["void"])
                          for e in found],
                         [(k1, False, True), (k2, True, False)])

    def refused(self, *args, **kw):
        with self.assertRaises(sc.InvalidAllocation) as caught:
            at.attempts_of(TASK, self.ledger(), *args, **kw)
        return str(caught.exception)

    def test_an_attempt_that_may_have_measured_is_refused(self):
        cases = {
            "left open": (dict(), [("open", None)]),
            "resumed": (dict(), [("open", None), ("close", "failed"),
                                 ("resume", None), ("close", "failed")]),
            "twice": (dict(), [("open", None), ("close", "failed"),
                               ("close", "failed")]),
            "pass": (dict(), [("open", None), ("close", "pass")]),
            "inconclusive": (dict(), [("open", None),
                                      ("close", "inconclusive")]),
            "cell": (dict(cells=["a-1.json.xz"]),
                     [("open", None), ("close", "failed")]),
            "partial": (dict(cells=["a-1.json.xz.partial"]),
                        [("open", None), ("close", "failed")]),
            "decisions": (dict(cells=["decisions-partial.json"]),
                          [("open", None), ("close", "failed")]),
            "inventory": (dict(inventory=dict(runs=[{}])),
                          [("open", None), ("close", "failed")]),
        }
        for name, (made, events) in cases.items():
            with self.subTest(name):
                self.ledger().unlink(missing_ok=True)
                out = self.out(name.replace(" ", "_"), **made)
                self.attempt(out, *events)
                self.assertIn("is not void", self.refused())

    def test_an_output_opened_twice_is_refused(self):
        # open/fail/open/pass would show the pass and hide the failure;
        # open/open/pass the same
        for name, events in (
                ("failpass", [("open", None), ("close", "failed"),
                              ("open", None), ("close", "pass")]),
                ("openopen", [("open", None), ("open", None),
                              ("close", "pass")])):
            with self.subTest(name):
                self.ledger().unlink(missing_ok=True)
                out = self.out(name, cells=["a-1.json.xz"])
                key = self.attempt(out, *events)
                self.assertIn("opened 2 times",
                              self.refused({key: out}))
                self.assertIn("opened 2 times", self.refused())

    def test_information_lines_are_not_attempts(self):
        out = self.out()
        key = at.attempt_id(out)
        self.attempt(out, ("info", None), ("info-end", None))
        self.assertEqual(self.refused({key: out})[:14], "judged attempt")
        self.assertEqual(at.attempts_of(TASK, self.ledger()), [])

    def test_a_missing_output_is_judged(self):
        out = Path(self.tmp.name) / "gone"
        self.attempt(out, ("open", None), ("close", "failed"))
        self.assertIn("output directory is missing", self.refused())

    def test_the_judged_attempt_must_be_in_the_ledger_and_its_output(self):
        out, other = self.out("a"), self.out("b")
        key = self.attempt(out, ("open", None), ("close", "pass"))
        self.assertIn("not in the ledger", self.refused({"nope": out}))
        self.assertIn("is judged, from", self.refused({key: other}))
        self.assertEqual(
            at.attempts_of(TASK, self.ledger(), {key: out})[0]["judged"],
            True)

    def test_one_attempt_is_of_one_output(self):
        out = self.out("a")
        key = self.attempt(out, ("open", None))
        tg.ledger_append(self.ledger(), event="close", stage="first",
                         table=TASK, attempt=key, candidate=CAND,
                         counts_file="c", counts="0" * 64, status="failed",
                         output=str(self.out("b")),
                         checkout=str(self.repo))
        self.assertIn("more than one output", self.refused())

    def test_no_ledger_and_another_task_are_refused(self):
        self.assertIn("no attempts ledger", self.refused())
        out = self.out()
        self.attempt(out, ("open", None), ("close", "failed"))
        with self.assertRaises(sc.InvalidAllocation):
            at.attempts_of("task31", self.ledger())
        # the lines of another table are not this task's
        self.assertEqual(
            at.attempts_of("task37-client", self.ledger()), [])

    def test_a_broken_chain_is_refused(self):
        out = self.out()
        self.attempt(out, ("open", None), ("close", "failed"))
        text = self.ledger().read_text().replace("failed", "passed")
        self.ledger().write_text(text)
        with self.assertRaises(sc.InvalidAllocation):
            at.attempts_of(TASK, self.ledger())


class Decisions(unittest.TestCase):
    def test_the_decisions_carry_what_the_disposition_gates_on(self):
        for task in (t37.MATRIX, t37.CLIENT, t37.DOWNSTREAM):
            out = m.assemble(*t37.grid_of(task, 3), task=task,
                             candidate=CAND)
            for key in ("status", "nondeterminism", "unresolved",
                        "cases", "complete", "acceptance_pairs"):
                self.assertIn(key, out, (task.name, key))
            self.assertEqual(out["status"], "pass")
            for case, record in out["cases"].items():
                self.assertIn("slopes", record, case)
                self.assertIn("constants", record, case)
                self.assertIsNotNone(record["slopes"], case)
                sizes = task.sizes(case)
                self.assertEqual(record["constants"] is None,
                                 0 not in sizes, case)
            self.assertTrue(m.results_markdown(out, task.label))
            self.assertEqual(m.status_code(out), 0)


if __name__ == "__main__":
    unittest.main()
