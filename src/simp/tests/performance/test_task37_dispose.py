#!/usr/bin/env python3
"""The TASK37 disposition (task37_dispose.py) on synthetic inputs: every
rule branch, the refusals, and the record/check round trip."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import acceptance as a
import task32_cases
import task33_dispose
import task37_cases as c
import task37_dispose as d
import timing_grid as tg

CAND = "c" * 40
RECORD = [dict(path="src/simp/src/Cond_rewr.sig", reason="adds a spec")]
D4 = c.d4()
HEAVY = c.INFEASIBLE[0]


def trow(cls="pass", first=None, stage2=False, followup=False):
    return dict(cls=cls, first=first or cls, stage2=stage2,
                followup=followup, earlier=[])


def ident(status="identical"):
    return dict(status=status, route="run",
                attributed=RECORD if status == "attributed" else [])


def arow(decision="pass", work="equal", pairs=3):
    return dict(decision=decision, work=work, pairs=pairs)


class Rule(unittest.TestCase):
    """`judge`: one cell."""

    NAME = "frag_create-100"

    def judge(self, identity="identical", alloc=None, timed=None,
              name=None, groups=None):
        return d.judge(name or self.NAME, ident(identity),
                       arow() if alloc is None else alloc, timed, set(D4),
                       groups)

    def test_unsampled_passes_on_identity_and_allocation(self):
        r = self.judge()
        self.assertEqual((r["status"], r["policy"]), ("pass", "stratified"))
        r = self.judge("attributed")
        self.assertEqual(r["status"], "pass")
        self.assertEqual(r["attribution"][0]["path"], RECORD[0]["path"])

    def test_identity(self):
        r = self.judge("different")
        self.assertEqual(r["status"], "fail")
        for status in ("unresolved", "inconclusive"):
            self.assertEqual(self.judge(status)["status"], "incomplete")

    def test_allocation(self):
        self.assertEqual(self.judge(alloc=arow("fail"))["status"], "fail")
        self.assertEqual(self.judge(alloc=arow(work="differs"))["status"],
                         "fail")
        for alloc in (arow("inconclusive", pairs=None),
                      arow(work="inconclusive"), arow(work=None)):
            self.assertEqual(self.judge(alloc=alloc)["status"],
                             "incomplete")
        r = d.judge(self.NAME, ident(), None, None, set())
        self.assertEqual(r["status"], "incomplete")

    def test_timing_decisions(self):
        self.assertEqual(self.judge(timed=trow())["status"], "pass")
        r = self.judge(timed=trow("fail"))
        self.assertEqual(r["status"], "fail")
        # a slowdown fails whatever the other gates say
        self.assertEqual(self.judge(alloc=arow(), timed=trow("fail"))[
            "failed"], ["timing: fail"])

    def test_inconclusive_never_passes(self):
        r = self.judge(timed=trow("inconclusive"))
        self.assertEqual((r["status"], r["owed"]), ("incomplete",
                                                    ["followup"]))
        r = self.judge(timed=trow("inconclusive", followup=True))
        self.assertEqual((r["owed"], r["blocked"]), (["attribution"], True))
        r = self.judge(timed=trow("control_limited"))
        self.assertEqual((r["status"], r["owed"]), ("incomplete",
                                                    ["stage2"]))
        r = self.judge(timed=trow("control_limited", stage2=True))
        self.assertEqual((r["owed"], r["blocked"]), (["attribution"], True))
        r = self.judge(timed=trow("protocol"))
        self.assertEqual((r["status"], r["owed"]), ("incomplete",
                                                    ["redraw"]))

    def test_d4(self):
        name = D4[0]
        r = self.judge(name=name, timed=trow("control_limited"))
        self.assertEqual((r["status"], r["policy"]), ("pass", "D4"))
        self.assertIn("stage 2 skipped", r["policy_note"])
        # a fresh pass and a fresh fail decide as for any cell
        self.assertEqual(self.judge(name=name, timed=trow())["policy"],
                         None)
        self.assertEqual(self.judge(name=name, timed=trow("fail"))[
            "status"], "fail")
        # not in the same way: the decisive first stage was not
        # control-limited
        r = self.judge(name=name, timed=trow("control_limited",
                                             first="inconclusive"))
        self.assertEqual(r["status"], "incomplete")
        self.assertEqual(self.judge(name=name, timed=trow(
            "inconclusive"))["status"], "incomplete")
        # D4 still needs identity and exact allocation
        self.assertEqual(self.judge(
            name=name, timed=trow("control_limited"),
            alloc=arow(work="differs"))["status"], "fail")
        self.assertEqual(self.judge(
            "different", name=name, timed=trow("control_limited"))[
            "status"], "fail")
        # and a cell that is not on the list has no such policy
        self.assertEqual(self.judge(timed=trow("control_limited"))[
            "status"], "incomplete")

    def test_d2(self):
        r = d.judge(HEAVY, ident(), None, None, set(), None)
        self.assertEqual((r["status"], r["policy"]), ("pass", "D2"))
        self.assertEqual(d.judge(HEAVY, ident("different"), None, None,
                                 set(), None)["status"], "fail")
        self.assertEqual(d.judge(HEAVY, ident("unresolved"), None, None,
                                 set(), None)["status"], "incomplete")
        none = dict(allocation=[], timing=[])
        r = d.judge(HEAVY, ident("attributed"), None, None, set(), none)
        self.assertEqual((r["status"], r["owed"]), ("incomplete",
                                                    ["attribution"]))
        some = dict(allocation=["x-1"], timing=["x-100"])
        r = d.judge(HEAVY, ident("attributed"), None, None, set(), some)
        self.assertEqual(r["status"], "pass")

    def test_measured_by(self):
        fam = d.family_of(HEAVY)
        cells = {n: ident("attributed") for n in c.CLIENT
                 if d.family_of(n) == fam and n not in c.INFEASIBLE}
        alloc = {n: arow() for n in cells}
        timed = {n: trow() for n in cells if n in c.CLIENT_SAMPLE}
        got = d.measured_by(HEAVY, cells, alloc, timed)
        self.assertTrue(got["allocation"] and got["timing"])
        self.assertTrue(all(d.size_of(n) <= 1000 for n in got["allocation"]))
        got = d.measured_by(HEAVY, cells, {}, {})
        self.assertEqual(got, dict(allocation=[], timing=[]))


class Cases(unittest.TestCase):
    def test_sets(self):
        self.assertEqual((len(c.MATRIX), len(c.CLIENT),
                          len(c.DOWNSTREAM)), (306, 278, 11))
        self.assertEqual(len(c.CLIENT_ALLOCATED), 245)
        self.assertEqual(len(D4), 13)
        self.assertTrue(set(D4) <= set(c.MATRIX_SAMPLE))
        self.assertTrue(set(c.FLAGGED) <= set(c.MATRIX_SAMPLE))
        self.assertTrue(set(c.CLIENT_SAMPLE) <= set(c.CLIENT) |
                        set(c.DOWNSTREAM))


def write(path, value):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(value))


def workload(name, cls):
    case, size = name.rsplit("-", 1)
    metric = dict(decision="pass", reason="")
    if cls == "fail":
        metric = dict(decision="fail", reason="slow")
    elif cls == "control_limited":
        metric = dict(decision="inconclusive", reason=tg.CONTROL)
    elif cls == "inconclusive":
        metric = dict(decision="inconclusive", reason="wide")
    return dict(case=case, size=int(size), protocol=cls != "protocol",
                metrics=dict(cpu=metric))


class Inputs(unittest.TestCase):
    """A complete synthetic input set in a temporary directory."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.counts = self.root / "counts"
        self.counts.mkdir()
        for name in d.COUNTS.values():
            (self.counts / name).write_text('{"counts": "%s"}' % name)
        patch = mock.patch.object(d, "COUNTS_DIR", self.counts)
        patch.start()
        self.addCleanup(patch.stop)
        self.attempts = []
        # The modules of the other parts may not be merged yet.
        present = tuple(n for n in d.CODE if (a.HERE / n).is_file())
        for target, value in (
                ("CODE", present),
                ("timing_engines", lambda: {
                    "task37-client": "ec", "task37-matrix": "em",
                    "task37-client-followup": "ecf",
                    "task37-matrix-followup": "emf"}),
                ("table_attempts", lambda *args: list(self.attempts))):
            patch = mock.patch.object(d, target, value)
            patch.start()
            self.addCleanup(patch.stop)
        self.build()

    def p(self, *parts):
        return self.root.joinpath(*parts)

    def header(self, **more):
        return dict(dict(candidate=CAND, baseline=a.BASE,
                         diagnostic=False), **more)

    def identity(self, name, names, **status):
        cells = {n: dict(status=status.get(n, "identical"), route="run",
                         attributed=[]) for n in names}
        write(self.p(name, "inventory.json"), self.header())
        write(self.p(name, "decisions.json"), self.header(
            status="identical", cells=cells, unaccounted=[],
            attributed=[]))

    def allocation(self, name, task, names, infeasible=(), pairs=3,
                   rows=None):
        write(self.p(name, "inventory.json"), self.header(
            task=task, pairs=pairs))
        rows = rows or {}
        write(self.p(name, "decisions.json"), self.header(
            complete=True, infeasible=sorted(infeasible), status="pass",
            rows=[dict(dict(case=n.rsplit("-", 1)[0],
                            size=int(n.rsplit("-", 1)[1]), pairs=pairs,
                            decision="pass", work="equal"),
                       **rows.get(n, {}))
                  for n in names]))

    def timing(self, name, table, names, classes=None, counts=None,
               attempt="a1", seal=None):
        classes = classes or {}
        counts = counts or d.COUNTS[table]
        file = self.counts / counts
        write(self.p(name, "inventory.json"), self.header(
            schema="%s-experiment-v1" % table, counts_file=counts,
            iterations_seal=seal or a.seal(file), attempt=attempt,
            environment=dict(loadavg=[0.1, 0.1, 0.1])))
        write(self.p(name, "decisions.json"), dict(
            status="inconclusive", retained_scaling=None,
            workloads=[workload(n, classes.get(n, "pass"))
                       for n in names]))
        (self.p(name) / "ledger.jsonl").touch()

    def receipts(self):
        for gate in d.GATES + (d.D7,):
            write(self.p(gate + ".json"), d.make_receipt(
                gate, CAND, "pass", 0))

    def build(self, client=None, matrix=None):
        self.identity("id-client", c.CLIENT)
        self.identity("id-matrix", c.MATRIX)
        self.identity("id-down", c.DOWNSTREAM)
        self.allocation("al-matrix", "task37-matrix", c.MATRIX)
        self.allocation("al-client", "task37-client", c.CLIENT_ALLOCATED,
                        c.INFEASIBLE)
        self.allocation("al-down", "task37-downstream", c.DOWNSTREAM)
        self.timing("t-client", "task37-client", c.CLIENT_SAMPLE, client)
        self.timing("t-matrix", "task37-matrix", c.MATRIX_SAMPLE, matrix)
        write(self.p("task32.json"), dict(
            candidate=CAND, status="pass", workloads={
                u: dict(status="pass", note="first", stages=[])
                for u in task32_cases.NAMES}))
        keys = task33_dispose.expected_storage()
        write(self.p("task33.json"), dict(
            schema=task33_dispose.SCHEMA, candidate=CAND, status="pass",
            decisions=[dict(case=k, kind=m, decision="pass", reason="",
                            owed=None) for k, m in keys],
            owed=[], attribution_needed=[], process_redraws=[]))
        self.receipts()

    def argv(self, mode, out, **drop):
        p = self.p
        found = {
            "identity-client": p("id-client"),
            "identity-matrix": p("id-matrix"),
            "identity-downstream": p("id-down"),
            "alloc-matrix": p("al-matrix"), "alloc-client": p("al-client"),
            "alloc-downstream": p("al-down"),
            "timing-client": p("t-client"), "timing-matrix": p("t-matrix"),
            "ledger-client": p("t-client", "ledger.jsonl"),
            "ledger-matrix": p("t-matrix", "ledger.jsonl"),
            "task32": p("task32.json"), "task33": p("task33.json"),
            "startup-gate": p("startup-gate.json"),
            "loading-simplib": p("loading-simpLib.json"),
            "loading-conglib": p("loading-congLib.json"),
            "d7-build": p("d7-build.json")}
        for k in drop:
            found.pop(k.replace("_", "-"))
        argv = ["--candidate", CAND[:12], "--" + mode, str(out)]
        for k, v in found.items():
            argv += ["--" + k, str(v)]
        return argv

    def run_cmd(self, mode="record", out=None, **drop):
        out = out or self.p("out")
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), \
                contextlib.redirect_stderr(stderr):
            rc = d.main(self.argv(mode, out, **drop))
        return rc, stdout.getvalue(), stderr.getvalue()


class Command(Inputs):
    def test_round_trip(self):
        rc, out, err = self.run_cmd()
        self.assertEqual((rc, err), (0, ""), out)
        self.assertIn("TASK37 disposition: pass", out.splitlines()[-1])
        record = json.loads((self.p("out") / "disposition.json").read_text())
        self.assertEqual(record["counts"]["fail"], 0)
        self.assertEqual(len(record["cells"]), 595)
        self.assertEqual(len(record["policies"]["D2"]), 33)
        self.assertEqual(len(record["task32"]), 15)
        self.assertEqual(record["allocation_pairs"], dict(
            matrix=3, client=3, downstream=3))
        self.assertEqual(record["candidate"], CAND)
        self.assertEqual(sorted(record["host_load"]), [
            "task37-client", "task37-matrix"])
        self.assertTrue((self.p("out") / "SUMMARY.txt").is_file())
        self.assertEqual(self.run_cmd("check", self.p("out"))[0], 0)
        # recording again refuses to replace
        self.assertEqual(self.run_cmd()[0], 3)

    def test_check_detects_changes(self):
        self.assertEqual(self.run_cmd()[0], 0)
        self.assertEqual(self.run_cmd("check", self.p("out"))[0], 0)
        self.allocation("al-down", "task37-downstream", c.DOWNSTREAM,
                        rows={c.DOWNSTREAM[0]: dict(work="differs")})
        rc, out, err = self.run_cmd("check", self.p("out"))
        self.assertEqual(rc, 3, out)
        self.assertIn("changed TASK37 disposition", err)

    def test_check_code_history(self):
        self.assertEqual(self.run_cmd()[0], 0)
        path = self.p("out", "disposition.json")
        record = json.loads(path.read_text())
        old = dict(sha256="0" * 64, bytes=1)
        record["code"]["acceptance.py"] = old
        path.write_text(json.dumps(record))
        rc, out, err = self.run_cmd("check", self.p("out"))
        self.assertEqual(rc, 3)
        self.assertIn("acceptance.py changed", err)
        with mock.patch.dict(d.HISTORY, {"acceptance.py": [old]}):
            self.assertEqual(self.run_cmd("check", self.p("out"))[0], 0)

    def test_slowdown_fails(self):
        name = c.MATRIX_SAMPLE[5]
        self.build(matrix={name: "fail"})
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 1, err)
        self.assertIn("FAIL cell %s: timing: fail" % name, out)

    def test_inconclusive_is_incomplete(self):
        name = c.CLIENT_SAMPLE[0]
        self.build(client={name: "inconclusive"})
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 2, err)
        record = json.loads((self.p("out") / "disposition.json").read_text())
        self.assertIn(dict(workload=name, owed="followup"), record["owed"])
        self.assertEqual(record["cells"][name]["status"], "incomplete")

    def test_d4_policy_recorded(self):
        self.build(matrix={n: "control_limited" for n in D4})
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 0, err)
        record = json.loads((self.p("out") / "disposition.json").read_text())
        self.assertEqual(record["policies"]["D4"], sorted(D4))
        self.assertIn("policy D4", out)

    def test_unsampled_cell_needs_no_timing(self):
        record = d.dispose  # the rule, through the command's records
        self.assertEqual(self.run_cmd()[0], 0)
        got = json.loads((self.p("out") / "disposition.json").read_text())
        name = next(n for n in c.MATRIX if n not in c.MATRIX_SAMPLE)
        self.assertEqual(got["cells"][name]["policy"], "stratified")
        self.assertIsNone(got["cells"][name]["timing"])

    def test_identity_different_fails(self):
        name = c.MATRIX[3]
        self.identity("id-matrix", c.MATRIX, **{name: "different"})
        self.assertEqual(self.run_cmd()[0], 1)

    def test_allocation_differs_fails(self):
        name = c.CLIENT_ALLOCATED[7]
        self.allocation("al-client", "task37-client", c.CLIENT_ALLOCATED,
                        c.INFEASIBLE, rows={name: dict(work="differs")})
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 1, err)
        self.assertIn("allocation: the work row differs", out)

    def test_void_attempts_are_recorded(self):
        self.attempts = [dict(attempt="x", status="inconclusive",
                              output="o", judged=False, void=True)]
        self.assertEqual(self.run_cmd()[0], 0)
        record = json.loads((self.p("out") / "disposition.json").read_text())
        self.assertTrue(record["timing_attempts"]["task37-client"][0][
            "void"])

    def test_a_refused_attempt_refuses(self):
        def refuse(*args):
            raise a.Blocked("attempt a2 is not void")
        with mock.patch.object(d, "table_attempts", refuse):
            rc, out, err = self.run_cmd()
        self.assertEqual(rc, 3)
        self.assertIn("not void", err)


class Followup(Inputs):
    def test_followup_replaces_cells(self):
        name = c.CLIENT_SAMPLE[1]
        self.build(client={name: "inconclusive"})
        self.timing("f-client", "task37-client", [name], counts=(
            "task37_client_iterations.json"), attempt="f1")
        argv = self.argv("record", self.p("out")) + [
            "--followup-client", str(self.p("f-client"))]
        with contextlib.redirect_stdout(io.StringIO()):
            rc = d.main(argv)
        self.assertEqual(rc, 0)
        record = json.loads((self.p("out") / "disposition.json").read_text())
        chain = record["cells"][name]["timing_chain"]
        self.assertTrue(chain["followup"])
        self.assertEqual(chain["earlier"], ["inconclusive"])

    def test_followup_outside_table_refused(self):
        self.timing("f-client", "task37-client", [c.MATRIX[0]])
        argv = self.argv("record", self.p("out")) + [
            "--followup-client", str(self.p("f-client"))]
        err = io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), \
                contextlib.redirect_stderr(err):
            self.assertEqual(d.main(argv), 3)
        self.assertIn("outside the table", err.getvalue())


class Refusals(Inputs):
    def refused(self, text, **drop):
        rc, out, err = self.run_cmd(**drop)
        self.assertEqual(rc, 3, out)
        self.assertIn(text, err)

    def test_each_input_is_required(self):
        for opt in ("identity_client", "identity_matrix",
                    "identity_downstream", "alloc_matrix", "alloc_client",
                    "alloc_downstream", "timing_client", "timing_matrix",
                    "ledger_client", "ledger_matrix", "task32", "task33",
                    "startup_gate", "loading_simplib", "loading_conglib"):
            with self.subTest(opt):
                rc, out, err = self.run_cmd(**{opt: None})
                self.assertEqual(rc, 3, out)
                self.assertIn("REFUSED", err)

    def test_d7_is_optional_and_not_a_gate(self):
        rc, out, err = self.run_cmd(d7_build=None)
        self.assertEqual(rc, 0, err)
        record = json.loads((self.p("out") / "disposition.json").read_text())
        self.assertIsNone(record["reported"]["d7_build"])
        self.p("out", "disposition.json").unlink()
        self.p("out", "SUMMARY.txt").unlink()
        self.p("out").rmdir()
        write(self.p("d7-build.json"), d.make_receipt(
            d.D7, CAND, "fail", 1))
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 0, err)

    def test_missing_files(self):
        self.p("al-matrix", "decisions.json").unlink()
        self.refused("partial")
        self.p("id-down", "inventory.json").unlink()
        self.refused("missing")

    def test_candidate_mismatch(self):
        write(self.p("id-matrix", "decisions.json"), dict(
            json.loads(self.p("id-matrix", "decisions.json").read_text()),
            candidate="d" * 40))
        self.refused("another candidate")

    def test_candidate_mismatch_in_each_kind(self):
        write(self.p("al-down", "inventory.json"), self.header(
            task="task37-downstream", pairs=3, candidate="d" * 40))
        self.refused("another candidate")

    def test_candidate_must_be_long_enough(self):
        argv = self.argv("record", self.p("out"))
        argv[1] = "abc"
        err = io.StringIO()
        with contextlib.redirect_stderr(err), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(d.main(argv), 3)

    def test_baseline_mismatch(self):
        write(self.p("t-matrix", "inventory.json"), dict(json.loads(
            self.p("t-matrix", "inventory.json").read_text()),
            baseline="e" * 40))
        self.refused("another baseline")

    def test_stale_counts_file(self):
        (self.counts / "task37_matrix_iterations.json").write_text("{}")
        self.refused("stale counts file")
        self.timing("t-matrix", "task37-matrix", c.MATRIX_SAMPLE)
        self.assertEqual(self.run_cmd()[0], 0)

    def test_wrong_counts_file(self):
        self.timing("t-matrix", "task37-matrix", c.MATRIX_SAMPLE,
                    counts="task37_client_iterations.json")
        self.refused("names the counts file")

    def test_timing_sample_is_exact(self):
        self.timing("t-matrix", "task37-matrix", c.MATRIX_SAMPLE[1:])
        self.refused("not the expected sample")
        self.timing("t-client", "task37-client",
                    list(c.CLIENT_SAMPLE) + [c.CLIENT[0]])
        self.refused("not the expected sample")

    def test_no_ledger(self):
        self.p("t-client", "ledger.jsonl").unlink()
        self.refused("no attempts ledger")

    def test_identity_cells_must_be_exact(self):
        self.identity("id-matrix", c.MATRIX[:-1])
        self.refused("not exactly the cells")

    def test_diagnostic_identity_refused(self):
        doc = json.loads(self.p("id-client", "decisions.json").read_text())
        doc["diagnostic"] = True
        write(self.p("id-client", "decisions.json"), doc)
        self.refused("diagnostic")

    def test_allocation_task_and_pairs(self):
        # a task's own pairs, not a constant: 3 pass, and so would 2
        self.allocation("al-down", "task37-downstream", c.DOWNSTREAM,
                        pairs=2)
        self.assertEqual(self.run_cmd()[0], 0)
        self.p("out", "disposition.json").unlink()
        self.p("out", "SUMMARY.txt").unlink()
        self.p("out").rmdir()
        # a passing row of fewer pairs than the task's is refused
        self.allocation("al-down", "task37-downstream", c.DOWNSTREAM,
                        rows={c.DOWNSTREAM[0]: dict(pairs=2)})
        self.refused("fewer than the task's 3 pairs")
        self.allocation("al-down", "task37-matrix", c.DOWNSTREAM)
        self.refused("not a task37-downstream grid")

    def test_allocation_incomplete_or_wrong_cells(self):
        self.allocation("al-matrix", "task37-matrix", c.MATRIX[:-1])
        self.refused("no row for")
        self.allocation("al-matrix", "task37-matrix", c.MATRIX)
        self.allocation("al-client", "task37-client", c.CLIENT_ALLOCATED)
        self.refused("infeasible cells are not")
        self.allocation("al-client", "task37-client", c.CLIENT,
                        c.INFEASIBLE)
        self.refused("not its")

    def test_task32_needs_candidate_and_units(self):
        doc = json.loads(self.p("task32.json").read_text())
        write(self.p("task32.json"), dict(doc, candidate="d" * 40))
        self.refused("another candidate")
        doc.pop("candidate")
        write(self.p("task32.json"), doc)
        self.refused("records no candidate")
        doc["candidate"] = CAND
        doc["workloads"].pop("rat")
        write(self.p("task32.json"), doc)
        self.refused("exactly the 15 units")

    def test_task32_rows(self):
        doc = json.loads(self.p("task32.json").read_text())
        doc["workloads"]["rat"] = dict(status="followup", note="x",
                                       stages=[])
        doc["status"] = "blocked"
        write(self.p("task32.json"), doc)
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 2, err)
        record = json.loads((self.p("out") / "disposition.json").read_text())
        self.assertIn(dict(workload="rat", owed="followup"),
                      record["owed"])
        doc["workloads"]["rat"] = dict(status="fail", note="x", stages=[])
        doc["status"] = "fail"
        write(self.p("task32.json"), doc)
        self.p("out", "disposition.json").unlink()
        self.p("out", "SUMMARY.txt").unlink()
        self.p("out").rmdir()
        self.assertEqual(self.run_cmd()[0], 1)

    def test_task33_rows(self):
        doc = json.loads(self.p("task33.json").read_text())
        doc["decisions"][0]["decision"] = "inconclusive"
        doc["status"] = "inconclusive"
        write(self.p("task33.json"), doc)
        self.assertEqual(self.run_cmd()[0], 2)
        self.p("out", "disposition.json").unlink()
        self.p("out", "SUMMARY.txt").unlink()
        self.p("out").rmdir()
        doc["decisions"][0]["decision"] = "fail"
        doc["status"] = "fail"
        write(self.p("task33.json"), doc)
        self.assertEqual(self.run_cmd()[0], 1)

    def test_task33_incomplete_or_inconsistent(self):
        doc = json.loads(self.p("task33.json").read_text())
        write(self.p("task33.json"), dict(doc, decisions=doc[
            "decisions"][1:]))
        self.refused("no decision for")
        write(self.p("task33.json"), dict(doc, status="fail"))
        self.refused("status is not that")
        write(self.p("task33.json"), dict(doc, schema="x"))
        self.refused("not a TASK33")

    def test_receipts(self):
        write(self.p("startup-gate.json"), d.make_receipt(
            "startup-gate", CAND, "fail", 1))
        self.assertEqual(self.run_cmd()[0], 1)
        write(self.p("startup-gate.json"), d.make_receipt(
            "startup-gate", CAND, "inconclusive", 2))
        self.p("out", "disposition.json").unlink()
        self.p("out", "SUMMARY.txt").unlink()
        self.p("out").rmdir()
        self.assertEqual(self.run_cmd()[0], 2)
        write(self.p("startup-gate.json"), d.make_receipt(
            "loading-simpLib", CAND, "pass", 0))
        self.refused("not a startup-gate receipt")
        write(self.p("startup-gate.json"), d.make_receipt(
            "startup-gate", "d" * 40, "pass", 0))
        self.refused("another candidate")

    def test_receipt_attributed_needs_text_and_report_seal(self):
        report = self.p("report.txt")
        report.write_text("x")
        write(self.p("startup-gate.json"), d.make_receipt(
            "startup-gate", CAND, "attributed", 0, [report],
            ["Cond_rewr.sig +2001 words"]))
        self.assertEqual(self.run_cmd()[0], 0)
        self.p("out", "disposition.json").unlink()
        self.p("out", "SUMMARY.txt").unlink()
        self.p("out").rmdir()
        report.write_text("changed")
        self.refused("changed or is missing")
        write(self.p("startup-gate.json"), d.make_receipt(
            "startup-gate", CAND, "attributed", 0))
        self.assertEqual(self.run_cmd()[0], 2)

    def test_make_receipt_checks(self):
        with self.assertRaises(ValueError):
            d.make_receipt("startup-gate", CAND, "pass", 1)
        with self.assertRaises(ValueError):
            d.make_receipt("nope", CAND, "pass", 0)

    def test_receipt_command(self):
        out = self.p("r.json")
        rc = d.main(["receipt", "--gate", "loading-congLib",
                     "--candidate", CAND, "--status", "pass", "--exit",
                     "0", "--out", str(out)])
        self.assertEqual(rc, 0)
        self.assertEqual(json.loads(out.read_text())["gate"],
                         "loading-congLib")


class Code(unittest.TestCase):
    PENDING = ("task37_matrix_identity.py", "task37_grid.py")

    def test_code_files_exist(self):
        for name in d.CODE:
            if name in self.PENDING:
                continue
            self.assertTrue((a.HERE / name).is_file(), name)

    def test_modules_imported_are_sealed(self):
        text = (a.HERE / "task37_dispose.py").read_text()
        import re
        found = set(re.findall(r"^(?:import|from) (\w+)", text, re.M))
        for name in found:
            if (a.HERE / (name + ".py")).is_file():
                self.assertIn(name + ".py", d.CODE)

    def test_no_pair_constant(self):
        text = (a.HERE / "task37_dispose.py").read_text()
        self.assertNotRegex(text, r"pairs[\"\]]*\s*>=\s*10")
        self.assertNotIn("am.PAIRS", text)

    def test_check_code_refusals(self):
        seals = {n: a.seal(a.HERE / n) for n in d.CODE
                 if n not in self.PENDING}
        with mock.patch.object(d, "CODE", tuple(seals)):
            d.check_code(seals)
            with self.assertRaises(ValueError):
                d.check_code({})
            changed = dict(seals, **{"acceptance.py": dict(
                sha256="0" * 64, bytes=1)})
            with self.assertRaises(ValueError):
                d.check_code(changed)

    def test_same_rev(self):
        self.assertTrue(d.same_rev("7e202dfbaa", "7e202dfbaa" + "1" * 30))
        self.assertFalse(d.same_rev("7e202df", "7e202dfbaa" + "1" * 30))
        self.assertFalse(d.same_rev("7e202dfbab", "7e202dfbaa" + "1" * 30))


if __name__ == "__main__":
    unittest.main()
