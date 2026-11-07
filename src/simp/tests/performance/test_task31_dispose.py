#!/usr/bin/env python3
"""The TASK31 decision per cell (task31_dispose.py): the rule on the
decisions of the three gates, the allocation contract, and the command with
its replays stood in for."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import acceptance as a
import task31_cases as c
import task31_dispose as d
import task31_grid as g
import timing_grid as tg

CAND = "c" * 40
NAMES = [g.name_of(*k) for k in g.every()]


SURVEY = {n: dict(zip(d.SURVEY_FIELDS, (1, 2, 3, 4, 5, 6)))
          for n in c.INFEASIBLE}
RECORD = [dict(path="src/simp/src/Cond_rewr.sig", reason="adds a spec")]


def identity(**status):
    cells = {}
    for n in NAMES:
        cells[n] = dict(status=status.get(n, "identical"), route="run",
                        attributed=RECORD if status.get(n) == "attributed"
                        else [])
        if n in c.INFEASIBLE:
            cells[n].update(route="derived from " + g.anchor(n))
    return dict(cells=cells, diagnostic=False, status="identical",
                unaccounted=[], attributed=[], attribution_table="t" * 64)


def allocation(**decision):
    return {n: decision.get(n, "pass") for n in NAMES
            if n not in c.INFEASIBLE}


def timing(**decision):
    return {n: decision.get(n, "pass") for n in c.SAMPLE}


class Rule(unittest.TestCase):
    def test_all_gates_passing_passes_every_cell(self):
        r = d.dispose(identity(), allocation(), timing(), SURVEY)
        self.assertEqual(r["status"], "pass")
        self.assertEqual(r["counts"]["pass"], 278)
        self.assertEqual(r["infeasible"], 33)

    def test_an_infeasible_cell_passes_by_identity_alone(self):
        r = d.dispose(identity(), allocation(), timing(), SURVEY)["cells"]
        found = r["tactic_full_complete-10000"]
        self.assertEqual((found["status"], found["note"]),
                         ("pass", "untimed, unallocated: infeasible"))
        self.assertIsNone(found["allocation"])
        self.assertIsNone(found["timing"])

    def test_an_infeasible_cell_with_a_different_closure_fails(self):
        r = d.dispose(identity(**{"tactic_full_complete-10000": "different"}),
                      allocation(), timing(), SURVEY)
        self.assertEqual(r["status"], "fail")
        self.assertEqual(r["cells"]["tactic_full_complete-10000"]["status"],
                         "fail")

    def test_identity_allocation_and_timing_are_each_required(self):
        sampled = c.SAMPLE[0]
        for kw, why in (
                (dict(i=dict(**{sampled: "different"})), "identity"),
                (dict(a={sampled: "fail"}), "allocation"),
                (dict(t={sampled: "fail"}), "timing")):
            r = d.dispose(identity(**kw.get("i", {})),
                          allocation(**kw.get("a", {})),
                          timing(**kw.get("t", {})), SURVEY)
            found = r["cells"][sampled]
            self.assertEqual((r["status"], found["status"]),
                             ("fail", "fail"), why)
            self.assertTrue(found["failed"][0].startswith(why), why)

    def test_inconclusive_and_control_limited_timing_is_incomplete(self):
        sampled = c.SAMPLE[0]
        for kind in ("inconclusive", "control_limited", "protocol"):
            r = d.dispose(identity(), allocation(), timing(
                **{sampled: kind}), SURVEY)
            self.assertEqual((r["status"], r["cells"][sampled]["status"]),
                             ("incomplete", "incomplete"), kind)
            self.assertEqual(r["cells"][sampled]["failed"], [], kind)

    def test_an_attributed_infeasible_cell_names_what_measured_it(self):
        name = "tactic_full_complete-10000"
        sib = {n: "attributed" for n in NAMES
               if g.case_of(n) == "tactic_full_complete" and n != name}
        sib.update({n: "attributed" for n in NAMES
                    if d.family_of(n) == "full" and n not in c.INFEASIBLE})
        r = d.dispose(identity(**sib, **{name: "attributed"}),
                      allocation(), timing(), SURVEY)["cells"][name]
        self.assertEqual(r["status"], "pass", r["missing"])
        self.assertIn("tactic_full_complete-100",
                      r["measured_by"]["timing"])
        self.assertTrue(r["measured_by"]["allocation"])
        self.assertEqual([x["path"] for x in r["attribution"]],
                         ["src/simp/src/Cond_rewr.sig"])
        r = d.dispose(identity(**{name: "attributed"}), allocation(),
                      timing(), SURVEY)["cells"][name]
        self.assertEqual(r["status"], "incomplete")

    def test_a_cell_outside_the_sample_needs_no_timing(self):
        other = next(n for n in NAMES
                     if n not in c.SAMPLE and n not in c.INFEASIBLE)
        r = d.dispose(identity(), allocation(), timing(),
                      SURVEY)["cells"][other]
        self.assertEqual((r["status"], r["timing"]), ("pass", None))

    def test_a_gate_with_no_decision_leaves_the_cell_incomplete(self):
        sampled = c.SAMPLE[0]
        alloc = allocation()
        del alloc[sampled]
        r = d.dispose(identity(), alloc, timing(), SURVEY)
        self.assertEqual(r["status"], "incomplete")
        self.assertEqual(r["cells"][sampled]["missing"],
                         ["allocation: no decision"])
        t = timing()
        del t[sampled]
        r = d.dispose(identity(), allocation(), t, SURVEY)
        self.assertEqual(r["cells"][sampled]["missing"],
                         ["timing: no decision"])

    def test_an_unresolved_identity_is_incomplete_and_a_fail_beats_it(self):
        r = d.dispose(identity(**{NAMES[0]: "unresolved"}), allocation(),
                      timing(), SURVEY)
        self.assertEqual(r["status"], "incomplete")
        r = d.dispose(identity(**{NAMES[0]: "unresolved",
                                  NAMES[1]: "different"}),
                      allocation(), timing(), SURVEY)
        self.assertEqual(r["status"], "fail")

    def test_a_diagnostic_identity_grid_is_refused(self):
        found = identity()
        found["diagnostic"] = True
        with self.assertRaises(ValueError):
            d.dispose(found, allocation(), timing(), SURVEY)

    def test_the_lines_name_failures_and_the_numbers_of_infeasible(self):
        r = d.dispose(identity(), allocation(**{c.SAMPLE[0]: "fail"}),
                      timing(), SURVEY)
        text = "\n".join(d.lines(r))
        self.assertIn("FAIL " + c.SAMPLE[0], text)
        self.assertIn("untimed, unallocated: infeasible", text)
        self.assertIn("tactic_full_complete-10000", text)
        self.assertIn("timeout 1800 s", text)
        self.assertIn("survey: op 4 s", text)

    def test_an_unaccounted_file_is_a_failure_line(self):
        found = identity()
        found.update(status="different", unaccounted=["src/x/Y.sml"])
        r = d.dispose(found, allocation(), timing(), SURVEY)
        self.assertEqual(r["status"], "fail")
        self.assertIn("FAIL identity grid: unaccounted difference "
                      "src/x/Y.sml", d.lines(r))
        found.update(status="inconclusive", unaccounted=[])
        self.assertEqual(d.dispose(found, allocation(), timing(),
                                   SURVEY)["status"], "incomplete")

    def test_the_verdict_names_attributions_and_attempts(self):
        found = identity()
        found.update(status="attributed", attributed=["src/x/Y.sig"])
        r = d.dispose(found, allocation(), timing(), SURVEY)
        r.update(timing_status="pass", candidate=CAND, harness="h" * 40,
                 attempts=dict(timing=[2, 1], identity=[3, 1]))
        text = d.verdict(r)
        for part in ("[src/x/Y.sig]", "timing 2 in the ledger, 1 of the "
                     "candidate", "identity 3, 1 of the candidate",
                     "infeasible 33 by identity", "harness " + "h" * 40):
            self.assertIn(part, text)


class Allocation(unittest.TestCase):
    def rows(self, *extra):
        return dict(rows=[dict(case=n.rsplit("-", 1)[0],
                               size=int(n.rsplit("-", 1)[1]),
                               decision="pass") for n in NAMES
                          if n not in c.INFEASIBLE] + list(extra))

    def test_the_contract_reads_one_decision_per_cell(self):
        found = d.allocation_rows(self.rows(), CAND)
        self.assertEqual(found, allocation())

    def test_the_candidate_is_checked_when_the_file_names_one(self):
        d.allocation_rows(dict(self.rows(), candidate=CAND), CAND)
        with self.assertRaises(ValueError):
            d.allocation_rows(dict(self.rows(), candidate="d" * 40), CAND)

    def test_malformed_unknown_repeated_and_infeasible_rows_are_refused(self):
        for bad in (
                dict(case="traversal_construct", size=0, decision="maybe"),
                dict(case="traversal_construct", size=0),
                dict(case="nonsense", size=0, decision="pass"),
                dict(case="tactic_full_complete", size=10000,
                     decision="pass"),
                dict(case="tactic_asm_complete", size=10, decision="pass")):
            with self.assertRaises(ValueError, msg=bad):
                d.allocation_rows(self.rows(bad), CAND)
        with self.assertRaises(ValueError):
            d.allocation_rows(dict(rows="no"), CAND)


class Command(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="task31-dispose-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for name in ("identity", "grid", "alloc"):
            (self.root / name).mkdir()
        a.save(self.root / "identity/decisions.json", dict(
            identity(), counts={}))
        a.save(self.root / "identity/inventory.json", dict(
            candidate=CAND, baseline=a.BASE))
        a.save(self.root / "grid/inventory.json", dict(
            candidate=CAND, baseline=a.BASE))
        self.survey = self.root / "survey.json"
        self.survey.write_text(json.dumps(dict(
            schema=d.SURVEY_SCHEMA, process_timeout=1800, cells=SURVEY)))
        self.timing = dict(status="pass", workloads=[], retained_scaling=None)
        self.classes = {"pass": list(c.SAMPLE)}
        a.save(self.root / "alloc/decisions.json", dict(
            candidate=CAND, rows=[dict(
                case=n.rsplit("-", 1)[0], size=int(n.rsplit("-", 1)[1]),
                decision="pass") for n in NAMES
                if n not in c.INFEASIBLE]))
        self.ledger = self.root / "attempts.jsonl"
        tg.ledger_append(self.ledger, event="open", stage="identity",
                         table=g.IDENTITY_TABLE, attempt="x",
                         candidate=CAND, output="o", checkout="c")
        self.patches = [
            mock.patch.object(d.grid, "identity_replay", lambda args: 0),
            mock.patch.object(d.grid.ENGINE.h, "attempts_file",
                              lambda args, appending, create=True:
                              self.ledger),
            mock.patch.object(d.grid.ENGINE, "replay", self.replay),
            mock.patch.object(d.tg, "classify", lambda decisions: dict(
                {k: [] for k in tg.CLASSES}, **self.classes))]
        for patch in self.patches:
            patch.start()
            self.addCleanup(patch.stop)
        self.write_timing()

    def write_timing(self):
        path = self.root / "grid/decisions.json"
        path.unlink(missing_ok=True)
        a.save(path, self.timing)

    def replay(self, args):
        self.replayed = args
        return 0

    def run_main(self, *more):
        argv = ["--identity", str(self.root / "identity"), "--grid",
                str(self.root / "grid"), "--pilot", str(self.root / "p"),
                "--allocation", str(self.root / "alloc"),
                "--survey", str(self.survey), *more]
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            return d.main(argv), out.getvalue()

    def test_a_clean_run_passes_and_prints_the_verdict_last(self):
        code, text = self.run_main()
        self.assertEqual(code, 0, text)
        last = text.strip().split("\n")[-1]
        self.assertTrue(last.startswith("TASK31 disposition: pass "), last)
        self.assertEqual(self.replayed.pilot, (self.root / "p").resolve())

    def test_a_failed_sample_cell_gives_status_1(self):
        self.classes = {"pass": list(c.SAMPLE[1:]), "fail": [c.SAMPLE[0]]}
        code, text = self.run_main()
        self.assertEqual(code, 1, text)
        self.assertIn("FAIL " + c.SAMPLE[0], text)

    def test_the_disposition_is_recorded_and_checked_again(self):
        record = self.root / "disposition.json"
        self.assertEqual(self.run_main("--record", str(record))[0], 0)
        self.assertEqual(self.run_main("--check", str(record))[0], 0)
        self.assertEqual(self.run_main("--record", str(record))[0],
                         tg.REFUSED)
        held = a.load(record)
        record.unlink()
        held["cells"][c.SAMPLE[0]]["status"] = "fail"
        a.save(record, held)
        self.assertEqual(self.run_main("--check", str(record))[0],
                         tg.REFUSED)

    def test_the_timing_grid_must_be_of_the_candidate_and_the_sample(self):
        (self.root / "grid/inventory.json").unlink()
        a.save(self.root / "grid/inventory.json", dict(
            candidate="e" * 40, baseline=a.BASE))
        self.assertEqual(self.run_main()[0], tg.REFUSED)
        (self.root / "grid/inventory.json").unlink()
        a.save(self.root / "grid/inventory.json", dict(
            candidate=CAND, baseline=a.BASE))
        self.classes = {"pass": list(c.SAMPLE[1:])}
        self.assertEqual(self.run_main()[0], tg.REFUSED)

    def test_the_survey_is_sealed_in_the_record_and_read_again(self):
        record = self.root / "disposition.json"
        self.assertEqual(self.run_main("--record", str(record))[0], 0)
        held = a.load(record)
        self.assertEqual(held["inputs"]["survey"], a.seal(self.survey))
        self.assertNotIn("cost", json.dumps(
            [x for x in held["cells"].values()
             if "survey" not in x]))
        self.survey.write_text(self.survey.read_text() + " ")
        self.assertEqual(self.run_main("--check", str(record))[0],
                         tg.REFUSED)

    def test_a_survey_that_misses_a_cell_is_refused(self):
        short = dict(SURVEY)
        short.pop("tactic_full_complete-10000")
        self.survey.write_text(json.dumps(dict(
            schema=d.SURVEY_SCHEMA, process_timeout=1800, cells=short)))
        self.assertEqual(self.run_main()[0], tg.REFUSED)
        self.survey.write_text(json.dumps(dict(
            schema="other", process_timeout=1800, cells=SURVEY)))
        self.assertEqual(self.run_main()[0], tg.REFUSED)

    def test_the_survey_is_required(self):
        with self.assertRaises(SystemExit), \
                contextlib.redirect_stderr(io.StringIO()):
            d.main(["--identity", "i", "--grid", "g", "--pilot", "p",
                    "--allocation", "a"])

    def test_a_follow_up_needs_a_declared_table(self):
        code, _ = self.run_main("--followup", str(self.root / "f"),
                                "--followup-pilot", str(self.root / "fp"))
        self.assertEqual(code, tg.REFUSED)


class Code(unittest.TestCase):
    def test_the_recorded_code_seals_are_checked(self):
        d.check_code(d.seals())
        bad = dict(d.seals(), **{"task31_grid.py": {"sha256": "0"}})
        with self.assertRaises(ValueError):
            d.check_code(bad)
        with mock.patch.dict(d.HISTORY, {"task31_grid.py": [
                {"sha256": "0"}]}):
            d.check_code(bad)

    def test_the_code_includes_the_attribution_and_the_follow_up(self):
        for name in ("task31_attribution.py", "task31_followup.py",
                     "task31_identity.py", "task31_snapshot.py"):
            self.assertIn(name, d.CODE if name != "task31_snapshot.py"
                          else d.CODE + ("task31_snapshot.py",))


if __name__ == "__main__":
    unittest.main()
