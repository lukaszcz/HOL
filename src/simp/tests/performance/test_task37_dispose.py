#!/usr/bin/env python3
"""The TASK37 disposition (task37_dispose.py) on synthetic inputs: every
rule branch, the refusals, the replays, the sharded timing join and the
record/check round trip. The identity decisions are made by the real
`task31_identity_grid.decide` (through task37_identity.py) and the attempts
by the real `void_attempts.attempts_of` where a test is about their format;
the other inputs are written in the format their producers write."""
import argparse
import contextlib
import io
import json
from pathlib import Path
import tempfile
import types
import unittest
from unittest import mock

import acceptance as a
import task32_cases
import task33_dispose
import task37_cases as c
import task37_dispose as d
import task37_grid as grid
import task37_identity as ti
import task37_load as load
import task31_identity_grid as idg
import test_task31_identity_grid as t31
import timing_grid as tg

CAND = "c" * 40
RECORD = [dict(path="src/simp/src/Cond_rewr.sig", reason="adds a spec")]
D4 = c.ATTRIBUTED
HEAVY = c.INFEASIBLE[0]
KEYS = grid.SHARD_KEYS


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
        cells = {n: ident("attributed") for n in c.CLIENT_CELLS
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
        self.assertEqual((len(c.MATRIX_CELLS), len(c.CLIENT_CELLS),
                          len(c.DOWNSTREAM_CELLS)), (306, 278, 11))
        self.assertEqual(len(c.CLIENT_ALLOCATED), 245)
        self.assertEqual(len(D4), 13)
        self.assertTrue(set(D4) <= set(c.MATRIX_SAMPLE))
        self.assertTrue(set(c.FLAGGED) <= set(c.MATRIX_SAMPLE))
        self.assertTrue(set(c.CLIENT_SAMPLE) <= set(c.CLIENT_CELLS) |
                        set(c.DOWNSTREAM_CELLS))

    def test_no_cell_set_is_defined_here(self):
        text = (a.HERE / "task37_dispose.py").read_text()
        for name in ("FLAGGED =", "INFEASIBLE =", "CLIENT_ALLOCATED =",
                     "MATRIX_SAMPLE =", "CLIENT_SAMPLE =", "def d4"):
            self.assertNotIn(name, text)


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


def identity_output(kind, names, status=None):
    """The inventory and the decisions of an identity grid of table `kind`
    over `names`, made by the real `decide` under the table's binding."""
    status = status or {}
    table = ti.tables()[kind]
    infeasible = set(table.infeasible)
    rows = []
    for n in names:
        if n in infeasible:
            continue
        case, size = c.split(n)
        found = status.get(n, "identical")
        rows.append(t31.row(
            case, size, found, files=table.sources, attributed=[
                dict(RECORD[0], path=RECORD[0]["path"])]
            if found == "attributed" else ()))
    found = t31.inventory(rows, expected=list(names))
    found["attributed"]["file"] = a.seal(c.REVIEWED_FILE)
    with ti.bound(table):
        return found, idg.decide(found)


class Inputs(unittest.TestCase):
    """A complete synthetic input set in a temporary directory."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.counts = self.root / "counts"
        self.counts.mkdir()
        for table in grid.TABLES.values():
            (self.counts / table.counts.name).write_text(
                '{"counts": "%s"}' % table.name)
        self.replays = []
        self.attempts = []
        self.broken = None
        for target, value in (
                ("COUNTS_DIR", self.counts),
                ("required_pairs", lambda task: 3),
                ("replay_identity", self.replay_identity),
                ("replay_timing", self.replay_timing),
                ("replay_allocation", self.replay_allocation),
                ("table_attempts", lambda *args: list(self.attempts))):
            patch = mock.patch.object(d, target, value)
            patch.start()
            self.addCleanup(patch.stop)
        self.build()

    def replay_identity(self, kind, root, repo, ledger):
        self.replays.append(("identity", kind, Path(root).name, ledger))
        if self.broken == ("identity", kind):
            raise ValueError("the %s grid does not replay" % kind)

    def replay_timing(self, engine, root, repo, ledger, pilot=None,
                      replaces_pilot=None):
        self.replays.append(("timing", engine.t.name, Path(root).name,
                             pilot, replaces_pilot))
        if self.broken == ("timing", engine.t.name):
            raise ValueError("the %s output does not replay" %
                             engine.t.name)

    def replay_allocation(self, root):
        self.replays.append(("allocation", Path(root).name))
        if self.broken == ("allocation", Path(root).name):
            raise ValueError("the allocation does not replay")

    def p(self, *parts):
        return self.root.joinpath(*parts)

    def header(self, **more):
        return dict(dict(candidate=CAND, baseline=a.BASE,
                         diagnostic=False), **more)

    def identity(self, name, kind, names, **status):
        inventory, decisions = identity_output(kind, names, status)
        write(self.p(name, "inventory.json"), inventory)
        write(self.p(name, "decisions.json"), decisions)
        self.p(name, "attempts.jsonl").touch()

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

    def timing(self, name, key, names=None, classes=None, counts=None,
               attempt="a1", seal=None, table=None):
        """The final stage of shard `key`: the fields the dispose reads of
        timing_grid's inventory and grid decision."""
        classes = classes or {}
        table = table or grid.TABLES[grid.name_of(key)]
        counts = counts or table.counts.name
        file = self.counts / counts
        write(self.p(name, "inventory.json"), self.header(
            schema=table.schema("experiment"), counts_file=counts,
            iterations_seal=seal or a.seal(file), attempt=attempt))
        write(self.p(name, "decisions.json"), dict(
            status="inconclusive", retained_scaling=None,
            workloads=[workload(n, classes.get(n, "pass"))
                       for n in (grid.PARTS[key] if names is None
                                 else names)]))
        (self.p(name) / "ledger.jsonl").touch()

    def receipts(self):
        for gate in d.GATES + (d.D7,):
            write(self.p(gate + ".json"), d.make_receipt(
                gate, CAND, "pass", 0))

    def build(self, classes=None):
        classes = classes or {}
        self.identity("id-client", "client", c.CLIENT_CELLS)
        self.identity("id-matrix", "matrix", c.MATRIX_CELLS)
        self.identity("id-down", "downstream", c.DOWNSTREAM_CELLS)
        self.allocation("al-matrix", "task37-matrix", c.MATRIX_CELLS)
        self.allocation("al-client", "task37-client", c.CLIENT_ALLOCATED,
                        c.INFEASIBLE)
        self.allocation("al-down", "task37-downstream", c.DOWNSTREAM_CELLS)
        for key in KEYS:
            self.timing("t-" + key, key, classes=classes)
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
        for stream in ("matrix", "client"):
            load.record(self.p("load-%s.jsonl" % stream), 1, stream, 1)

    def argv(self, mode, out, drop=(), extra=()):
        p = self.p
        found = {
            "identity-client": p("id-client"),
            "identity-matrix": p("id-matrix"),
            "identity-downstream": p("id-down"),
            "alloc-matrix": p("al-matrix"), "alloc-client": p("al-client"),
            "alloc-downstream": p("al-down"),
            "task32": p("task32.json"), "task33": p("task33.json"),
            "startup-gate": p("startup-gate.json"),
            "loading-simplib": p("loading-simpLib.json"),
            "loading-conglib": p("loading-congLib.json"),
            "d7-build": p("d7-build.json")}
        for k in drop:
            found.pop(k.replace("_", "-"), None)
        argv = ["--candidate", CAND[:12], "--" + mode, str(out),
                "--repo", str(self.root)]
        for k, v in found.items():
            argv += ["--" + k, str(v)]
        for kind in c_kinds():
            if "identity_" + kind not in drop:
                argv += ["--identity-ledger", "%s=%s" % (
                    kind, p("id-" + {"downstream": "down"}.get(kind, kind),
                            "attempts.jsonl"))]
        for key in KEYS:
            if "timing_" + key in drop:
                continue
            argv += ["--timing", "%s=%s" % (key, p("t-" + key)),
                     "--ledger", "%s=%s" % (
                         key, p("t-" + key, "ledger.jsonl"))]
        argv += ["--load", "client-1=" + str(p("load-client.jsonl")),
                 "--load", "matrix-1=" + str(p("load-matrix.jsonl"))]
        return argv + list(extra)

    def run_cmd(self, mode="record", out=None, drop=(), extra=()):
        out = out or self.p("out")
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), \
                contextlib.redirect_stderr(stderr):
            rc = d.main(self.argv(mode, out, drop, extra))
        return rc, stdout.getvalue(), stderr.getvalue()

    def reset(self):
        for name in ("disposition.json", "SUMMARY.txt"):
            self.p("out", name).unlink(missing_ok=True)
        if self.p("out").exists():
            self.p("out").rmdir()

    def record(self):
        return json.loads((self.p("out") / "disposition.json").read_text())


def realattempts(engine, root, repo, ledger):
    return d.attempts_of(argparse.Namespace(repo=repo, ledger=ledger),
                         engine, d.judged_attempts(engine, root))


def c_kinds():
    return d.KINDS


class Command(Inputs):
    def test_round_trip(self):
        rc, out, err = self.run_cmd()
        self.assertEqual((rc, err), (0, ""), out)
        self.assertIn("TASK37 disposition: pass", out.splitlines()[-1])
        record = self.record()
        self.assertEqual(record["counts"]["fail"], 0)
        self.assertEqual(len(record["cells"]), 595)
        self.assertEqual(len(record["policies"]["D2"]), 33)
        self.assertEqual(len(record["task32"]), 15)
        self.assertEqual(record["allocation_pairs"], dict(
            matrix=3, client=3, downstream=3))
        self.assertEqual(record["candidate"], CAND)
        self.assertEqual(sorted(record["shards"]),
                         sorted(grid.TABLES))
        self.assertTrue((self.p("out") / "SUMMARY.txt").is_file())
        self.assertEqual(self.run_cmd("check", self.p("out"))[0], 0)
        # recording again refuses to replace
        self.assertEqual(self.run_cmd()[0], 3)

    def test_every_input_is_replayed(self):
        self.assertEqual(self.run_cmd()[0], 0)
        found = [r[:2] for r in self.replays]
        self.assertEqual(sorted(found), sorted(
            [("identity", k) for k in d.KINDS] +
            [("timing", n) for n in grid.TABLES] +
            [("allocation", n) for n in ("al-matrix", "al-client",
                                         "al-down")]))
        ledgers = {r[1]: r[3] for r in self.replays if r[0] == "identity"}
        self.assertEqual(ledgers["matrix"], self.p("id-matrix",
                                                   "attempts.jsonl"))

    def test_a_failed_replay_refuses_the_disposition(self):
        for broken in (("identity", "matrix"), ("identity", "client"),
                       ("timing", "task37-matrix-3"),
                       ("timing", "task37-client-2"),
                       ("allocation", "al-client")):
            with self.subTest(broken):
                self.broken = broken
                self.reset()
                rc, out, err = self.run_cmd()
                self.assertEqual(rc, 3, out)
                self.assertIn("does not replay", err)
                self.assertFalse(self.p("out", "disposition.json").exists())

    def test_check_detects_changes(self):
        self.assertEqual(self.run_cmd()[0], 0)
        self.assertEqual(self.run_cmd("check", self.p("out"))[0], 0)
        self.allocation("al-down", "task37-downstream", c.DOWNSTREAM_CELLS,
                        rows={c.DOWNSTREAM_CELLS[0]: dict(work="differs")})
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
        self.build(classes={name: "fail"})
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 1, err)
        self.assertIn("FAIL cell %s: timing: fail" % name, out)

    def test_inconclusive_is_incomplete(self):
        name = c.CLIENT_SAMPLE[0]
        self.build(classes={name: "inconclusive"})
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 2, err)
        self.assertIn(dict(workload=name, owed="followup"),
                      self.record()["owed"])
        self.assertEqual(self.record()["cells"][name]["status"],
                         "incomplete")

    def test_d4_policy_recorded(self):
        self.build(classes={n: "control_limited" for n in D4})
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 0, err)
        self.assertEqual(self.record()["policies"]["D4"], sorted(D4))
        self.assertIn("policy D4", out)

    def test_unsampled_cell_needs_no_timing(self):
        self.assertEqual(self.run_cmd()[0], 0)
        got = self.record()
        name = next(n for n in c.MATRIX_CELLS
                    if n not in c.MATRIX_SAMPLE)
        self.assertEqual(got["cells"][name]["policy"], "stratified")
        self.assertIsNone(got["cells"][name]["timing"])

    def test_identity_different_fails(self):
        name = c.MATRIX_CELLS[3]
        self.identity("id-matrix", "matrix", c.MATRIX_CELLS,
                      **{name: "different"})
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
        found = self.record()["timing_attempts"]
        self.assertEqual(sorted(found), sorted(grid.TABLES))
        self.assertTrue(found["task37-client-1"][0]["void"])

    def test_a_refused_attempt_refuses(self):
        def refuse(*args):
            raise a.Blocked("attempt a2 is not void")
        with mock.patch.object(d, "table_attempts", refuse):
            rc, out, err = self.run_cmd()
        self.assertEqual(rc, 3)
        self.assertIn("not void", err)

    def test_the_host_load_is_reported_and_never_a_gate(self):
        self.assertEqual(self.run_cmd()[0], 0)
        record = self.record()
        self.assertEqual(sorted(record["host_load"]),
                         ["client-1", "matrix-1"])
        self.assertEqual(record["host_load"]["matrix-1"]["samples"], 1)
        self.assertIn("load-matrix-1", record["inputs"])
        # Without it the disposition is the same, but for the report.
        self.reset()
        rc, out, err = self.run_cmd(extra=())
        self.reset()
        argv = [x for x in self.argv("record", self.p("out"))]
        i = argv.index("--load")
        del argv[i:i + 4]
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(d.main(argv), 0)
        self.assertEqual(self.record()["host_load"], {})
        # An absurd load changes no decision.
        self.reset()
        self.p("load-matrix.jsonl").write_text(json.dumps(dict(
            stream="matrix", epoch=1, time="t", load=[999.0] * 3,
            runnable=999, cpus=16)) + "\n")
        self.assertEqual(self.run_cmd()[0], 0)
        self.assertEqual(self.record()["host_load"]["matrix-1"][
            "max_load"], [999.0] * 3)

    def test_a_missing_or_malformed_load_recording_is_refused(self):
        self.p("load-matrix.jsonl").unlink()
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 3)
        self.assertIn("load recording", err)
        self.p("load-matrix.jsonl").write_text("")
        self.reset()
        self.assertEqual(self.run_cmd()[0], 3)
        rc, out, err = self.run_cmd(extra=["--load", "noequals"])
        self.assertEqual(rc, 3)
        self.assertIn("--load needs KEY=PATH", err)


class Shards(Inputs):
    def refused(self, text, **kw):
        rc, out, err = self.run_cmd(**kw)
        self.assertEqual(rc, 3, out)
        self.assertIn(text, err)
        self.assertFalse(self.p("out").exists())

    def test_every_shard_is_required(self):
        for key in KEYS:
            with self.subTest(key):
                self.refused("every shard is required",
                             drop=("timing_" + key,))

    def test_a_shard_needs_its_ledger(self):
        self.p("t-matrix-2", "ledger.jsonl").unlink()
        self.refused("no attempts ledger")

    def test_unknown_or_repeated_shards_are_refused(self):
        self.refused("--timing needs KEY=PATH with KEY one of", extra=[
            "--timing", "matrix-9=%s" % self.p("t-matrix-1")])
        self.refused("--timing names matrix-1 twice", extra=[
            "--timing", "matrix-1=%s" % self.p("t-matrix-1")])
        self.refused("--timing needs KEY=PATH", extra=["--timing", "x"])

    def test_a_shard_has_exactly_its_part(self):
        names = list(grid.PARTS["matrix-1"])
        self.timing("t-matrix-1", "matrix-1", names[1:])
        self.refused("not its part of the sample")
        self.timing("t-matrix-1", "matrix-1", names + [
            grid.PARTS["matrix-2"][0]])
        self.refused("not its part of the sample")
        # Another shard's cells in its place: the right count, the wrong
        # cells.
        self.timing("t-matrix-1", "matrix-1", grid.PARTS["matrix-2"][:len(
            names)])
        self.refused("not its part of the sample")

    def test_the_union_must_be_the_sample(self):
        with mock.patch.dict(grid.PARTS, {
                "client-2": grid.PARTS["client-2"][:-1]}):
            self.timing("t-client-2", "client-2")
            with mock.patch.object(d.grid, "partition", lambda k: ()):
                self.refused("do not join to the sample")

    def test_the_shards_may_not_overlap(self):
        shared = grid.PARTS["matrix-1"][0]
        parts = dict(grid.PARTS, **{"matrix-2": grid.PARTS["matrix-2"] + (
            shared,)})
        with mock.patch.object(grid, "PARTS", parts):
            self.timing("t-matrix-2", "matrix-2", parts["matrix-2"])
            self.refused("shards overlap")

    def test_the_counts_file_is_the_shards_own_and_committed(self):
        (self.counts / "task37_matrix_3_iterations.json").write_text("{}")
        self.refused("stale counts file")
        self.timing("t-matrix-3", "matrix-3")
        self.assertEqual(self.run_cmd()[0], 0)
        self.reset()
        self.timing("t-matrix-3", "matrix-3",
                    counts="task37_matrix_4_iterations.json")
        self.refused("names the counts file")
        self.timing("t-matrix-3", "matrix-3")
        # the un-sharded name of before is no counts file
        (self.counts / "task37_matrix_iterations.json").write_text("{}")
        self.timing("t-matrix-3", "matrix-3",
                    counts="task37_matrix_iterations.json")
        self.refused("names the counts file")

    def test_a_shard_of_another_candidate_or_baseline_is_refused(self):
        inv = json.loads(self.p("t-client-1", "inventory.json").read_text())
        write(self.p("t-client-1", "inventory.json"), dict(
            inv, candidate="d" * 40))
        self.refused("another candidate")
        write(self.p("t-client-1", "inventory.json"), dict(
            inv, baseline="e" * 40))
        self.refused("another baseline")

    def test_each_shards_attempts_use_its_own_engine(self):
        seen = []

        def attempts(engine, root, repo, ledger):
            seen.append((engine.t.name, Path(root).name, Path(ledger)))
            return []
        with mock.patch.object(d, "table_attempts", attempts):
            self.assertEqual(self.run_cmd()[0], 0)
        self.assertEqual(sorted(seen), sorted(
            (n, "t-" + n[7:], self.p("t-" + n[7:], "ledger.jsonl"))
            for n in grid.TABLES))

    def test_the_timing_decision_of_a_shard_reaches_its_cells(self):
        name = grid.PARTS["matrix-4"][2]
        self.build(classes={name: "fail"})
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 1, err)
        self.assertEqual(self.record()["cells"][name]["timing"], "fail")


class Followup(Inputs):
    """A declared follow-up of a shard."""

    KEY = "client-1"

    def setUp(self):
        super().setUp()
        self.name = self.KEY and grid.name_of(self.KEY)
        self.cell = grid.PARTS[self.KEY][1]
        base = grid.GRIDS[self.name]
        self.table = grid.followup_table(self.KEY, [self.cell], base)
        engine = tg.Grid(self.table, doc="x")
        for target, key, value in (
                (grid.GRIDS, self.table.name, engine),
                (grid.TABLES, self.table.name, self.table)):
            patch = mock.patch.dict(target, {key: value})
            patch.start()
            self.addCleanup(patch.stop)
        (self.counts / self.table.counts.name).write_text("{}")
        self.build(classes={self.cell: "inconclusive"})
        self.timing("f-out", self.KEY, [self.cell], table=self.table,
                    attempt="f1")
        write(self.p("pilot", "x"), 1)
        write(self.p("fpilot", "x"), 1)

    def extra(self, **drop):
        found = {"--followup": "%s=%s" % (self.KEY, self.p("f-out")),
                 "--pilot": "%s=%s" % (self.KEY, self.p("pilot")),
                 "--followup-pilot": "%s=%s" % (self.KEY,
                                                self.p("fpilot"))}
        out = []
        for k, v in found.items():
            if k[2:] not in drop:
                out += [k, v]
        return out

    def test_followup_replaces_cells_and_is_replayed(self):
        self.attempts = [dict(attempt="x", status="pass", output="o",
                              judged=True, void=False)]
        rc, out, err = self.run_cmd(extra=self.extra())
        self.assertEqual(rc, 0, err)
        chain = self.record()["cells"][self.cell]["timing_chain"]
        self.assertTrue(chain["followup"])
        self.assertEqual(chain["earlier"], ["inconclusive"])
        found = [r for r in self.replays if r[1] == self.table.name]
        self.assertEqual(len(found), 1)
        self.assertEqual(found[0][3:], (self.p("fpilot").resolve(),
                                        self.p("pilot").resolve()))
        self.assertEqual(len(self.record()["timing_attempts"][self.name]),
                         2)

    def test_without_a_follow_up_the_cell_is_owed_one(self):
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 2, err)
        self.assertIn(dict(workload=self.cell, owed="followup"),
                      self.record()["owed"])

    def test_a_follow_up_needs_both_pilots(self):
        for drop in ("pilot", "followup-pilot"):
            with self.subTest(drop):
                self.reset()
                rc, out, err = self.run_cmd(extra=self.extra(**{drop: 1}))
                self.assertEqual(rc, 3, out)
                self.assertIn("needs --pilot and --followup-pilot", err)

    def test_a_pilot_without_a_follow_up_is_refused(self):
        rc, out, err = self.run_cmd(extra=self.extra(followup=1))
        self.assertEqual(rc, 3, out)
        self.assertIn("with no --followup", err)

    def test_the_follow_up_must_be_the_declared_cells(self):
        self.timing("f-out", self.KEY, [grid.PARTS[self.KEY][2]],
                    table=self.table, attempt="f1")
        rc, out, err = self.run_cmd(extra=self.extra())
        self.assertEqual(rc, 3, out)
        self.assertIn("not the declared follow-up", err)

    def test_a_follow_up_nobody_declared_is_refused(self):
        with mock.patch.dict(grid.GRIDS):
            del grid.GRIDS[self.table.name]
            rc, out, err = self.run_cmd(extra=self.extra())
        self.assertEqual(rc, 3, out)
        self.assertIn("no follow-up is declared", err)

    def test_a_stale_follow_up_counts_file_is_refused(self):
        (self.counts / self.table.counts.name).write_text("{x}")
        rc, out, err = self.run_cmd(extra=self.extra())
        self.assertEqual(rc, 3, out)
        self.assertIn("stale counts file", err)


class Formats(Inputs):
    """What the dispose reads is what the producers write."""

    def test_identity_decisions_are_the_real_ones(self):
        inventory, decisions = identity_output("downstream",
                                               c.DOWNSTREAM_CELLS)
        self.assertEqual(decisions["schema"], idg.DECISIONS)
        self.assertEqual(sorted(decisions["cells"]),
                         sorted(c.DOWNSTREAM_CELLS))
        for key in ("status", "candidate", "baseline", "diagnostic",
                    "unaccounted", "attributed", "cells"):
            self.assertIn(key, decisions)
        found = d.load_identity(
            self.p("id-down"), "x", c.DOWNSTREAM_CELLS, CAND, "downstream",
            self.p("id-down", "attempts.jsonl"), self.root)
        self.assertEqual(found["status"], decisions["status"])
        self.assertEqual(found["unaccounted"], decisions["unaccounted"])

    def test_an_attributed_cell_carries_its_real_record(self):
        name = c.MATRIX_CELLS[10]
        self.identity("id-matrix", "matrix", c.MATRIX_CELLS,
                      **{name: "attributed"})
        self.assertEqual(self.run_cmd()[0], 0)
        found = self.record()["cells"][name]["attribution"]
        self.assertEqual(found, [dict(path=RECORD[0]["path"],
                                      reason=RECORD[0]["reason"])])

    def test_the_infeasible_client_cells_derive_in_the_real_decision(self):
        inventory, decisions = identity_output("client", c.CLIENT_CELLS)
        for n in c.INFEASIBLE:
            self.assertIn("derived from", decisions["cells"][n]["route"])
        self.assertEqual(len(decisions["cells"]), 278)

    def test_an_identity_grid_of_another_reviewed_table_is_refused(self):
        inv = json.loads(self.p("id-matrix", "inventory.json").read_text())
        inv["attributed"]["file"] = a.seal(
            a.HERE / "task31_attributed.json")
        write(self.p("id-matrix", "inventory.json"), inv)
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 3, out)
        self.assertIn("not the committed", err)

    def test_the_identity_ledger_is_required(self):
        self.p("id-client", "attempts.jsonl").unlink()
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 3, out)
        self.assertIn("no attempts ledger", err)
        self.reset()
        rc, out, err = self.run_cmd(drop=("identity_client",))
        self.assertEqual(rc, 3, out)

    def test_allocation_rows_are_those_of_cell_rows(self):
        import allocation_matrix as am
        task = am.task_named("task31")
        found = am.assemble(set(), {}, {}, a.BASE, task, CAND)
        for key in ("rows", "complete", "infeasible", "candidate",
                    "baseline"):
            self.assertIn(key, found)
        cells = {("traversal_construct", 0)}
        found = am.assemble(cells, {}, {}, a.BASE, task, CAND)
        row, = found["rows"]
        self.assertEqual(sorted(row), ["case", "decision", "pairs", "size",
                                       "work"])
        self.assertIn(row["decision"], d.DECISIONS)
        self.assertIn(row["work"], d.WORK)
        self.assertEqual(found["infeasible"], sorted(
            "%s-%d" % k for k in task.infeasible))

    def test_the_fields_read_from_timing_grid_exist_there(self):
        text = (a.HERE / "timing_grid.py").read_text()
        for field in ("counts_file", "iterations_seal", "grid_inventory",
                      "grid_decisions", "remeasured", "plan", "attempt"):
            self.assertIn(field, text)
        self.assertEqual(
            tg.Table.schema(grid.TABLES["task37-matrix-1"], "experiment"),
            "task37-matrix-1-experiment-v1")
        self.assertTrue(d.is_extension(dict(
            schema=grid.TABLES["task37-matrix-1"].schema("extension"))))

    def test_the_attempts_are_those_of_the_real_function(self):
        """A ledger written by the engine: the judged attempt is found, and
        an attempt of another output that is not void is refused (R-1)."""
        key = "matrix-1"
        engine = grid.GRIDS["task37-" + key]
        ledger = self.p("real.jsonl")
        root = self.p("t-" + key)
        inventory = a.load(root / "inventory.json")
        inventory["candidate"] = CAND
        engine.record_attempt(ledger, "open", "first", inventory, root,
                              self.root)
        engine.close_attempt(ledger, "first", inventory, root, self.root,
                             "pass")
        with mock.patch.object(d, "table_attempts", types.FunctionType(
                d.table_attempts.__code__, d.__dict__)) if False \
                else contextlib.nullcontext():
            pass
        found = realattempts(engine, root, self.root, ledger)
        self.assertEqual([(x["attempt"], x["judged"], x["void"])
                          for x in found], [("a1", True, False)])
        other = dict(inventory, attempt="zz")
        engine.record_attempt(ledger, "open", "first", other,
                              self.p("nowhere"), self.root)
        engine.close_attempt(ledger, "first", other, self.p("nowhere"),
                             self.root, "pass")
        with self.assertRaises(ValueError) as caught:
            realattempts(engine, root, self.root, ledger)
        self.assertIn("not void", str(caught.exception))


class Replays(unittest.TestCase):
    """The replay functions call the producers' replays as they take them."""

    def test_the_identity_replay(self):
        import task37_identity
        seen = []
        with mock.patch.object(task37_identity, "identity_replay",
                               lambda args: seen.append(args) or 1):
            d.replay_identity("matrix", Path("/x/out"), Path("/repo"),
                              Path("/l"))
        args, = seen
        self.assertEqual((args.table, args.output, args.repo, args.ledger,
                          args.attributed), ("matrix", Path("/x/out"),
                                             Path("/repo"), Path("/l"),
                                             None))
        with mock.patch.object(task37_identity, "identity_replay",
                               lambda args: 3):
            with self.assertRaises(ValueError):
                d.replay_identity("matrix", Path("/x"), None, None)

    def test_the_timing_replay(self):
        seen = []
        engine = types.SimpleNamespace(
            replay=lambda args: seen.append(args) or 2)
        d.replay_timing(engine, Path("/x/out"), Path("/repo"), Path("/l"),
                        pilot=Path("/p"), replaces_pilot=Path("/q"))
        args, = seen
        self.assertEqual((args.output, args.partial, args.repo, args.ledger,
                          args.pilot, args.replaces_pilot),
                         (Path("/x/out"), False, Path("/repo"), Path("/l"),
                          Path("/p"), Path("/q")))
        broken = types.SimpleNamespace(replay=lambda args: 3)
        with self.assertRaises(ValueError):
            d.replay_timing(broken, Path("/x"), None, None)

    def test_the_allocation_replay(self):
        import allocation_matrix as am
        seen = []
        with mock.patch.object(am, "replay",
                               lambda args: seen.append(args) or 0):
            d.replay_allocation(Path("/x/out"))
        self.assertEqual(seen[0].output, Path("/x/out"))
        with mock.patch.object(am, "replay", lambda args: 3):
            with self.assertRaises(ValueError):
                d.replay_allocation(Path("/x"))

    def test_the_required_pairs_are_the_tasks_own(self):
        import allocation_matrix as am
        task = types.SimpleNamespace(pairs=3)
        with mock.patch.object(am, "task_named", lambda n: task):
            self.assertEqual(d.required_pairs("task37-matrix"), 3)


class Pairs(Inputs):
    def test_the_inventory_pairs_are_the_tasks_own(self):
        # a run of other pairs than the task's is refused, whatever it says
        self.allocation("al-down", "task37-downstream", c.DOWNSTREAM_CELLS,
                        pairs=2)
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 3, out)
        self.assertIn("not the task's 3", err)
        self.allocation("al-down", "task37-downstream", c.DOWNSTREAM_CELLS,
                        pairs=10)
        self.assertEqual(self.run_cmd()[0], 3)

    def test_a_passing_row_of_fewer_pairs_is_refused(self):
        self.allocation("al-down", "task37-downstream", c.DOWNSTREAM_CELLS,
                        rows={c.DOWNSTREAM_CELLS[0]: dict(pairs=2)})
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 3, out)
        self.assertIn("fewer than the task's 3 pairs", err)

    def test_the_task_and_the_cells(self):
        self.allocation("al-down", "task37-matrix", c.DOWNSTREAM_CELLS)
        self.assertIn("not a task37-downstream grid", self.run_cmd()[2])
        self.allocation("al-matrix", "task37-matrix", c.MATRIX_CELLS[:-1])
        self.assertIn("no row for", self.run_cmd()[2])
        self.allocation("al-matrix", "task37-matrix", c.MATRIX_CELLS)
        self.allocation("al-client", "task37-client", c.CLIENT_ALLOCATED)
        self.assertIn("infeasible cells are not", self.run_cmd()[2])
        self.allocation("al-client", "task37-client", c.CLIENT_CELLS,
                        c.INFEASIBLE)
        self.assertIn("not its", self.run_cmd()[2])
        self.p("al-client", "decisions.json").unlink()
        self.assertIn("partial", self.run_cmd()[2])

    def test_candidate_mismatch_in_each_kind(self):
        write(self.p("al-down", "inventory.json"), self.header(
            task="task37-downstream", pairs=3, candidate="d" * 40))
        rc, out, err = self.run_cmd()
        self.assertEqual(rc, 3)
        self.assertIn("another candidate", err)

    def test_identity_cells_must_be_exact_and_not_a_diagnostic(self):
        self.identity("id-matrix", "matrix", c.MATRIX_CELLS[:-1])
        self.assertIn("not exactly the cells", self.run_cmd()[2])
        self.identity("id-matrix", "matrix", c.MATRIX_CELLS)
        doc = json.loads(self.p("id-client", "decisions.json").read_text())
        doc["diagnostic"] = True
        write(self.p("id-client", "decisions.json"), doc)
        self.assertIn("diagnostic", self.run_cmd()[2])
        self.identity("id-client", "client", c.CLIENT_CELLS)
        self.p("id-down", "inventory.json").unlink()
        self.assertIn("missing", self.run_cmd()[2])

    def test_identity_candidate_mismatch(self):
        write(self.p("id-matrix", "decisions.json"), dict(
            json.loads(self.p("id-matrix", "decisions.json").read_text()),
            candidate="d" * 40))
        self.assertIn("another candidate", self.run_cmd()[2])


class Refusals(Inputs):
    def refused(self, text, **drop):
        rc, out, err = self.run_cmd(drop=tuple(drop))
        self.assertEqual(rc, 3, out)
        self.assertIn(text, err)

    def test_each_input_is_required(self):
        for opt in ("identity_client", "identity_matrix",
                    "identity_downstream", "alloc_matrix", "alloc_client",
                    "alloc_downstream", "task32", "task33",
                    "startup_gate", "loading_simplib", "loading_conglib"):
            with self.subTest(opt):
                rc, out, err = self.run_cmd(drop=(opt,))
                self.assertEqual(rc, 3, out)
                self.assertIn("REFUSED", err)

    def test_d7_is_optional_and_not_a_gate(self):
        rc, out, err = self.run_cmd(drop=("d7_build",))
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

    def test_candidate_must_be_long_enough(self):
        argv = self.argv("record", self.p("out"))
        argv[1] = "abc"
        err = io.StringIO()
        with contextlib.redirect_stderr(err), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(d.main(argv), 3)

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
    def test_code_files_exist(self):
        for name in d.CODE:
            self.assertTrue((a.HERE / name).is_file(), name)

    def test_the_engine_and_module_names_are_the_merged_ones(self):
        self.assertIn("task37_identity.py", d.CODE)
        self.assertNotIn("task37_matrix_identity.py", d.CODE)
        self.assertNotIn("task30_dispose.py", d.CODE)
        text = (a.HERE / "task37_dispose.py").read_text()
        for stale in ("matrix_identity", "ENGINES_BY_KIND",
                      "timing_engines", "task37_grid.ENGINES",
                      "task37_client_iterations", "iterations.json\"",
                      "task37_matrix_iterations"):
            self.assertNotIn(stale, text)

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
        seals = {n: a.seal(a.HERE / n) for n in d.CODE}
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
