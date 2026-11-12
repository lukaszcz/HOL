#!/usr/bin/env python3
"""The TASK33 storage driver (task33_storage.py), its decision rules
(task33_rules.py) and its disposal (task33_dispose.py): the rules on
synthetic validated summaries, the driver on fake snapshots and fake
probe processes, the joined disposition and the snapshot disposal on a
fake tree."""
import argparse
import contextlib
import copy
from fractions import Fraction
import io
import json
from pathlib import Path
import shutil
import sys
import unittest
from unittest import mock

import acceptance as acc
import task33_cases as cases33
import task33_dispose as dispose
import task33_offline as offline
import task33_records as records
import task33_rules as rules
import task33_storage as st
import task32_downstream as dw
import test_task32_downstream as t32
import test_task33_downstream as t33
import test_task33_records as rt

setUpModule = t32.setUpModule

SIZES = (0, 1, 100)
M = 4


def retext(text, root):
    """The records' fake paths (rt's) in the side's own root."""
    return text.replace("/snap/base", str(root))


class WorldS(t33.World33):
    """The TASK33 world with the storage probes played: the records of
    each probe kind from the record helpers, in the side's own root,
    editable per (unit, side)."""

    def __init__(self, tmp):
        super().__init__(tmp)
        self.edits = {}  # (unit, side) -> function on the record list

    def records_of(self, name, env, side):
        sw = dict(graph_extra="T33_GRAPH_EXTRA" in env,
                  leak="T33_LEAK" in env, hook="T33_HOOK" in env)
        sw = {k: v for k, v in sw.items() if v}
        probe = env["T33_KIND"]
        sizes = [int(x) for x in env.get("T33_SIZES", "").split(",") if x]
        m = int(env.get("T33_M", "0"))
        if probe == "graph":
            return rt.graph_run(sizes, **sw)
        if probe == "release":
            return self.release(m, sw)
        if probe == "ext":
            return rt.ext_run(m, sizes)
        if name.startswith("trivial-"):
            return rt.trivial_run(probe)
        return rt.load_run("registry", probe, **sw)

    @staticmethod
    def release(m, sw):
        """A release run; a leaked kind keeps every discarded object, but
        the no-op kind has nothing to keep."""
        run = rt.release_run(m, **sw)
        if not sw.get("leak"):
            return run
        first = rt.find(run, "live", phase="noop.before")
        last = rt.find(run, "release", release="noop")
        run[first:last + 1] = rt.release_rows("release", "release",
                                              ("noop",), m)
        return run

    def output(self, unit, root, probe_dir, differ=False):
        raise AssertionError("storage units are played by `launch`")

    def launch(self, argv, cwd, env, timeout, out_path, fds=()):
        side = "cand" if str(self.roots["cand"]) in argv[0] else "base"
        name = self.unit_name(argv[-1], env)
        run = self.records_of(name, env, side)
        edit = self.edits.get((name, side))
        if edit:
            run = edit(copy.deepcopy(run))
        self.counter += 1
        self.calls.append((name, side, dict(env), list(argv), str(cwd)))
        root = self.roots[side]
        loaded = list(t33.CHECK.get(env["T33_KIND"], []))
        files = [["T32Report.sml", str(Path(argv[-2]).parent)],
                 ["T33Load.sml", str(cwd)]]
        stats = dict(schema=dw.STATS_SCHEMA, nongc_usr=1.0, nongc_sys=0.05,
                     gc_usr=0.04, gc_sys=0.01, gc_time=0.05,
                     holdir=str(root), loaded_before=t33.heap_modules(
                         "bin/hol.state"), loaded=loaded, files=files,
                     **t32.STAT_FIELDS)
        if argv[-1] == "T33Ext":
            stats["loaded"].append("simpExtLib")
        text = retext(rt.text(run, noise=False), root)
        Path(out_path).write_text("banner\n" + text)
        Path(env["T32_STATS"]).write_text(json.dumps(stats) + "\n")
        return dict(exit=0, timed_out=False, wall=1.03, utime=0.9,
                    stime=0.1, maxrss=10 ** 8, survivors=[])

    @staticmethod
    def unit_name(probe, env):
        name = {"T33Registry": "registry-" + env["T33_KIND"],
                "T33Trivial": "trivial-" + env["T33_KIND"],
                "T33Graph": "graph", "T33Release": "release",
                "T33Ext": "ext"}[probe]
        for sw, tag in (("T33_GRAPH_EXTRA", "graph_extra"),
                        ("T33_LEAK", "leak"), ("T33_HOOK", "hook")):
            if sw in env:
                name += "+" + tag
        return name

    def probes(self, root, folder, env, timeout, fds, sealed=None,
               modules=None):
        out = super().probes(root, folder, env, timeout, fds, sealed,
                             modules)
        out["modules"] = list(modules or [])
        return out


class Base34(t33.Base33):
    def setUp(self):
        previous = dw.use_table("task33")
        self.addCleanup(dw.use_table, previous)
        self.dir = t32.tempfile.TemporaryDirectory(prefix="t33s-test-")
        self.addCleanup(self.dir.cleanup)
        self.world = WorldS(self.dir.name)
        for patch in self.world.patches():
            patch.start()
            self.addCleanup(patch.stop)
        self.addCleanup(self.remove_lock)

    def args(self, name, **extra):
        w = self.world
        values = dict(
            repo=w.repo, base_root=w.roots["base"],
            cand_root=w.roots["cand"], manifest=w.manifest,
            timing_counts=None, storage_counts=None,
            output=w.tmp / name, scratch=w.tmp / "scratch", timeout=60,
            verify_argv=[sys.executable, "-c", "pass"], no_verify=False,
            authorize_measurements=True, only=[], sizes=SIZES, m=M,
            m0=M, pilot=None, first=None, stage=None, ledger=None,
            followup_counts=None)
        values.update(extra)
        return argparse.Namespace(**values)

    def once(self, unit, side, edit):
        """`edit` on the first process of the unit on the side only."""
        done = []

        def first(run):
            if done:
                return run
            done.append(1)
            return edit(run)
        self.world.edits[unit, side] = first

    def run_stage(self, name, mode, **extra):
        args = self.args(name, **extra)
        return args, st.run(args, st.info_spec(args, mode))


def summ(run, controls=()):
    return records.validate(rt.text(run, noise=False), controls=controls,
                            root=rt.ROOT)


def graph_of(sizes=SIZES, **extra):
    return rt.graph_run(sizes, **extra)


def grow(run, g, n, by=1):
    """The graph record of kind g at size n grown by `by` words (as built
    and canonical)."""
    i = rt.find(run, "graph", graph=g, n=n)
    x = run[i]
    return rt.edit(run, i, words=x["words"] + by, union=x["union"] + by,
                   canon_words=x["canon_words"] + by,
                   canon_union=x["canon_union"] + by)


def row_of(rows, kind):
    return [r for r in rows if r["kind"] == kind][0]


class S1(unittest.TestCase):
    def test_equal_graphs_pass(self):
        b = [summ(graph_of())] * 3
        for g in rules.GRAPH_GATED:
            r = rules.s1_kind(b, b, g)
            self.assertEqual((r["decision"], r["owed"]),
                             ("pass", None), (g, r["reason"]))

    def test_one_more_word_at_one_size_fails(self):
        b = [summ(graph_of())] * 3
        c = [summ(grow(graph_of(), "fragment", 100))] * 3
        r = rules.s1_kind(b, c, "fragment")
        self.assertEqual(r["decision"], "fail", r["reason"])
        self.assertIn("size 100", r["reason"])
        self.assertEqual(rules.s1_kind(b, c, "merge")["decision"], "pass")

    def test_fewer_words_pass(self):
        b = [summ(graph_of())] * 3
        c = [summ(grow(graph_of(), "fragment", 100, -1))] * 3
        self.assertEqual(rules.s1_kind(b, c, "fragment")["decision"],
                         "pass")

    def test_a_non_repeatable_series_escalates(self):
        b = [summ(graph_of()), summ(graph_of()),
             summ(grow(graph_of(), "fragment", 100))]
        r = rules.s1_kind(b, b, "fragment")
        self.assertEqual((r["decision"], r["owed"]),
                         ("inconclusive", "extend"))
        paired = rules.s1_kind(b, b, "fragment", paired=True)
        self.assertEqual(paired["owed"], None)

    def test_too_small_sizes_leave_the_as_built_rows_inconclusive(self):
        b = [summ(graph_of((0, 1, 10)))] * 3
        r = rules.s1_kind(b, b, "fragment")
        self.assertEqual(r["decision"], "inconclusive")
        self.assertIn("as-built", r["reason"])

    def test_a_kind_without_gateable_coverage_is_inconclusive(self):
        b = [dict(summ(graph_of()), gateable_coverage=dict(fragment=[0]))
             ] * 3
        r = rules.s1_kind(b, b, "fragment")
        self.assertEqual(r["decision"], "inconclusive")
        self.assertFalse(r["as_built_gated"])
        self.assertEqual(rules.s1_kind(b, b, "merge")["decision"], "pass")

    def test_an_anchor_moved_on_the_candidate_fails(self):
        b = [summ(graph_of())] * 3
        c = [dict(x, anchor_moved=[dict(kind="fragment", n=100)])
             for x in b]
        r = rules.s1_kind(b, c, "fragment")
        self.assertEqual(r["decision"], "fail", r["reason"])

    def test_different_sizes_block(self):
        b = [summ(graph_of())] * 3
        c = [summ(graph_of((0, 1, 10, 100)))] * 3
        self.assertEqual(rules.s1_kind(b, c, "fragment")["decision"],
                         "blocked")


def release_of(m=M, noop_leak=0, leak=False):
    run = rt.release_run(m)
    if noop_leak or leak:
        i, j = rt.find(run, "live", phase="noop.before"), rt.find(
            run, "release", release="noop")
        run[i:j + 1] = rt.release_rows("release", "release", ("noop",), m,
                                       noop_leak)
        if leak:
            run = WorldS.release(m, dict(leak=True))
    return summ(run, ("leak",) if leak else ())


class R1(unittest.TestCase):
    def test_equal_releases_pass(self):
        b = [release_of()] * 3
        for r in rules.r1_rows(b, b):
            self.assertEqual(r["decision"], "pass", (r["kind"],
                                                     r["reason"]))

    def test_the_leak_control_fails(self):
        b, c = [release_of()] * 3, [release_of(leak=True)] * 3
        rows = rules.r1_rows(b, c)
        self.assertEqual(row_of(rows, "simpset")["decision"], "fail")
        self.assertEqual(row_of(rows, "weak")["decision"], "pass")

    def test_an_unresolved_noop_floor_is_inconclusive(self):
        b, c = [release_of()] * 3, [release_of(noop_leak=1)] * 3
        r = rules.r1_kind(b, c, "simpset")
        self.assertEqual((r["decision"], r["owed"]),
                         ("inconclusive", "followup"))
        self.assertIn("resolution", r["reason"])

    def test_a_small_held_object_cannot_resolve(self):
        run = release_of()
        c = [dict(run, held=dict(run["held"], simpset=Fraction(5)))] * 3
        r = rules.r1_kind([run] * 3, c, "simpset")
        self.assertEqual((r["decision"], r["owed"]),
                         ("inconclusive", "followup"))
        self.assertIn("20", r["reason"])

    def test_held_readings_not_comparable_are_left_out(self):
        run = release_of()
        mark = lambda ok: dict(run, release=dict(run["release"], simpset=dict(
            run["release"]["simpset"], held_comparable=ok)))
        small = dict(mark(False), held=dict(run["held"],
                                            simpset=Fraction(5)))
        r = rules.r1_kind([run] * 2 + [small], [run] * 3, "simpset")
        self.assertEqual(r["decision"], "pass", r["reason"])
        r = rules.r1_kind([small] * 3, [run] * 3, "simpset")
        self.assertEqual(r["decision"], "inconclusive")
        self.assertIn("no comparable held", r["reason"])

    def test_a_baseline_residual_is_inconclusive(self):
        c = [release_of()] * 3
        b = [release_of(leak=True)] * 3
        r = rules.r1_kind(b, c, "simpset")
        self.assertEqual((r["decision"], r["owed"]),
                         ("inconclusive", "followup"))


def registry_of(kind="state-empty", missing=(), **fields):
    run = rt.load_run("registry", kind)
    i = rt.find(run, "registry")
    if missing:
        run[i] = rt.registry("registry", kind, missing=missing)
    return summ(rt.edit(run, i, **fields))


class S2L(unittest.TestCase):
    def test_equal_registries_pass_with_a_zero_delta(self):
        b = [registry_of()] * 3
        self.assertEqual(rules.s2_kind(b, b, "state-empty", 0)["decision"],
                         "pass")

    def test_a_total_change_other_than_the_declared_fails(self):
        b = [registry_of()] * 3
        r = rules.s2_kind(b, b, "state-empty", 5)
        self.assertEqual(r["decision"], "fail", r["reason"])
        self.assertIn("declared 5", r["reason"])

    def test_the_declared_change_passes(self):
        b = [registry_of()] * 3
        grown = rt.anchored()
        grown["total"] = [t + 7 for t in grown["total"]]
        c = [registry_of(anchored=grown)] * 3
        self.assertEqual(rules.s2_kind(b, c, "state-empty", 7)["decision"],
                         "pass")

    def test_a_growing_exclusive_part_fails(self):
        b = [registry_of()] * 3
        c = [registry_of(anchored=rt.anchored(reps=(6, 6, 6)))] * 3
        r = rules.s2_kind(b, c, "state-empty", 0)
        self.assertEqual(r["decision"], "fail", r["reason"])

    def test_a_shrinking_exclusive_part_passes(self):
        b = [registry_of()] * 3
        c = [registry_of(anchored=rt.anchored(reps=(4, 4, 4)))] * 3
        self.assertEqual(rules.s2_kind(b, c, "state-empty", 0)["decision"],
                         "pass")

    def test_a_non_repeatable_total_escalates(self):
        a = rt.anchored(reps=(5, 6, 5))
        b = [registry_of(anchored=a)] * 3
        r = rules.s2_kind(b, b, "state-empty", 0)
        self.assertEqual((r["decision"], r["owed"]),
                         ("inconclusive", "extend"))

    def test_a_total_computed_on_one_side_fails(self):
        b = [registry_of()] * 3
        c = [registry_of(missing=("Opening",))] * 3
        self.assertEqual(rules.s2_kind(b, c, "state-empty", 0)["decision"],
                         "fail")

    def test_no_total_anywhere_is_reported(self):
        b = [registry_of(missing=("Opening",))] * 3
        r = rules.s2_kind(b, b, "state-empty", None)
        self.assertEqual(r["decision"], "reported")

    def test_a_total_without_a_declared_delta_is_a_value_error(self):
        b = [registry_of()] * 3
        with self.assertRaises(ValueError):
            rules.s2_kind(b, b, "state-empty", None)

    def test_each_total_needs_exactly_one_declared_entry(self):
        entries = rules.total_deltas(DECLARED)
        self.assertEqual(rules.declared_delta(
            entries, "bin/hol.state", "state-empty"), 0)
        with self.assertRaises(ValueError):
            rules.declared_delta(entries, "bin/other", "state-empty")
        with self.assertRaises(ValueError):
            rules.declared_delta(entries + entries, "bin/hol.state",
                                 "state-empty")

    def test_the_earlier_dict_form_covers_the_state_heap_only(self):
        entries = rules.total_deltas(dict(s2=dict(total_delta=dict(
            value=754))))
        self.assertEqual(rules.declared_delta(
            entries, "bin/hol.state", "first-use"), 754)
        with self.assertRaises(ValueError):
            rules.declared_delta(entries, "bin/hol.state0", "first-use")


class L1L3(unittest.TestCase):
    def mask(self, side, path):
        return path.replace(str(side), "ROOT")

    def test_equal_lists_pass_and_a_difference_fails(self):
        b = [registry_of()] * 3
        c = [registry_of(listeners=["DB", "extra"])] * 3
        self.assertEqual(rules.l3_kind(b, b, "state-empty")["decision"],
                         "pass")
        r = rules.l3_kind(b, c, "state-empty")
        self.assertEqual(r["decision"], "fail", r["reason"])
        self.assertEqual(r["differences"]["listeners"]["only_cand"],
                         ["extra"])

    def test_a_different_loaded_set_fails_l1(self):
        b = [registry_of()] * 3
        c = [registry_of(loaded=["Abbrev"])] * 3
        r = rules.l1_kind(b, c, "state-empty", lambda s, p: p)
        self.assertEqual(r["decision"], "fail", r["reason"])
        self.assertEqual(rules.l1_kind(b, b, "state-empty",
                                       lambda s, p: p)["decision"], "pass")

    def test_a_process_that_differs_from_its_own_side_is_unstable(self):
        b = [registry_of(), registry_of(),
             registry_of(listeners=["x"])]
        r = rules.l3_kind(b, b, "state-empty")
        self.assertNotEqual(r["decision"], "pass")


def ext_of():
    return summ(rt.ext_run(M, SIZES))


class E(unittest.TestCase):
    def test_the_extension_checks_pass_e1(self):
        self.assertEqual(rules.e1_ext([ext_of()])["decision"], "pass")
        self.assertEqual(rules.e1_ext([])["decision"], "blocked")

    def test_e2b_gates_the_residual_of_the_extension_alone(self):
        r = rules.e2b([ext_of()] * 3)
        self.assertEqual((r["case"], r["kind"], r["decision"]),
                         ("E2", "b", "pass"), r["reason"])

    def test_e2a_compares_the_ordinary_rows(self):
        graph = [summ(graph_of())] * 3
        ext = [ext_of()] * 3
        self.assertEqual(rules.e2a(ext, graph)["decision"], "pass")
        bad = [summ(grow(graph_of(), "fragment", 100))] * 3
        self.assertEqual(rules.e2a(ext, bad)["decision"], "fail")
        other = [summ(graph_of((0, 1)))] * 3
        self.assertEqual(rules.e2a(ext, other)["decision"], "blocked")

    def test_e2c_names_what_the_extension_registers(self):
        plain = [registry_of()] * 3
        ext = [ext_of()] * 3
        text = json.dumps(DECLARED["e2c"])
        r = rules.e2c(ext, plain, text)
        self.assertIn(r["decision"], ("pass", "fail"), r["reason"])
        gone = [registry_of(loaded=["Abbrev", "simpLib", "extra"])] * 3
        r = rules.e2c(ext, gone, text)
        self.assertEqual(r["decision"], "fail", r["reason"])


DECLARED = {
    "s2": {"total_delta": [
        dict(heap="bin/hol.state", kinds=None, value=0, observed={},
             mechanism="none"),
        dict(heap="bin/hol.state0", kinds=None, value=0, observed={},
             mechanism="none")]},
    "e2c": {"extension_state": [{"name": "simpExtLib",
                                 "created_by": "simpExtLib.register"}]}}


class Chain34(Base34):
    """The stages of the storage gate on fake processes, with the
    declaration patched to the list form of design 8.5."""

    def setUp(self):
        super().setUp()
        patch = mock.patch.object(st.offline, "load_declared",
                                  lambda *a: copy.deepcopy(DECLARED))
        patch.start()
        self.addCleanup(patch.stop)

    def commit(self, path):
        w = self.world
        t32.git(w.repo, "add", str(path.relative_to(w.repo)))
        t32.git(w.repo, "commit", "-q", "-m", "counts " + path.name)

    def timing_counts(self):
        w = self.world
        sides, mseal = dw.pins_of(self.args("x"))
        path = w.repo / "src/simp/tests/performance/task33_counts.json"
        path.write_text(json.dumps(dict(
            schema=dw.COUNTS_SCHEMA, kind="first", table="task33",
            base=sides["base"]["pin"], cand=sides["cand"]["pin"],
            manifest=mseal, code=dw.code_seals(),
            reps={n: 1 for n in cases33.NAMES},
            references={n: "0" * 64 for n in cases33.NAMES})))
        self.commit(path)
        return path

    def stage(self, name, mode, **extra):
        args, report = self.run_stage(name, mode, **extra)
        self.assertTrue(report["success"], report.get("failure"))
        return args, report

    def info_stages(self):
        _, smoke = self.stage("smoke", "smoke")
        _, pilot = self.stage("pilot", "pilot", sizes=SIZES, m0=M)
        _, control = self.stage("control", "control",
                                pilot=self.world.tmp / "pilot")
        return smoke, pilot, control

    def predeclare(self, **extra):
        w = self.world
        timing = self.timing_counts()
        args = self.args("pre", timing_counts=timing, smoke=w.tmp / "smoke",
                         pilot=w.tmp / "pilot", control=w.tmp / "control",
                         offline=[], **extra)
        data = st.predeclare_run(args)
        out = w.repo / "src/simp/tests/performance/" \
            "task33_storage_counts.json"
        out.write_text(dw.dumps(data))
        self.commit(out)
        return args, data, out

    def decide(self, name="first", **extra):
        args, data, out = self.predeclare_done
        a = self.args(name, timing_counts=args.timing_counts,
                      storage_counts=out, **extra)
        return a, st.run(a, st.run_spec(a))


    def go(self):
        self.info_stages()
        self.predeclare_done = self.predeclare()
        return self.decide()


    def prepared(self):
        self.info_stages()
        self.predeclare_done = self.predeclare()


    def replayed(self, report, a):
        return st.replay_chain(report["output"],
                               counts=a.storage_counts)[-1]



class Smoke(Base34):
    def test_a_smoke_run_measures_every_unit_once_per_side(self):
        args, report = self.run_stage("smoke", "smoke")
        self.assertTrue(report["success"], report.get("failure"))
        self.assertTrue(report["outcome"]["facts"]["ok"])
        self.assertEqual(len(report["runs"]), 2 * len(st.UNITS) - 1)


class Stages(Chain34):
    def test_the_chain_to_a_pass(self):
        smoke, pilot, control = self.info_stages()
        self.assertTrue(control["outcome"]["negative_control"]["detected"],
                        control["outcome"]["controls"])
        args, data, out = self.predeclare()
        self.assertEqual(data["decision"]["m"], M)
        self.assertFalse(data["capped"])

    def test_the_run_passes_and_replays_byte_identically(self):
        a, report = self.go()
        self.assertTrue(report["success"], report.get("failure"))
        out = report["outcome"]
        self.assertEqual(dw.stage_status(out["results"]), "pass")
        self.assertEqual(st.exit_of(report), 0)
        self.assertEqual(out["owed"], [])
        last = self.replayed(report, a)
        self.assertEqual(last["info"]["exit"], "pass")
        folder = Path(report["output"])
        again = st.outcome(last["report"], [
            (e, st.check_run(folder, last["report"], e))
            for e in last["report"]["runs"]], folder)
        self.assertEqual(dw.dumps(again), dw.dumps(out))

    def test_a_changed_outcome_fails_the_replay(self):
        a, report = self.go()
        path = Path(report["output"]) / "downstream.json"
        saved = path.read_text()
        data = json.loads(saved)
        key = sorted(data["outcome"]["results"])[0]
        data["outcome"]["results"][key]["reason"] += "!"
        path.write_text(dw.dumps(data))
        with self.assertRaises(dw.Refusal):
            self.replayed(report, a)
        path.write_text(saved)
        self.replayed(report, a)

    def test_the_plus_one_word_fails_the_run(self):
        self.prepared()
        self.world.edits["graph", "cand"] = lambda run: grow(
            run, "fragment", 100)
        a, report = self.decide()
        self.assertTrue(report["success"], report.get("failure"))
        rows = report["outcome"]["results"]
        self.assertEqual(rows["S1:fragment"]["decision"], "fail")
        self.assertEqual(rows["S1:merge"]["decision"], "pass")
        self.assertEqual(st.exit_of(report), 1)
        self.assertEqual(self.replayed(report, a)["info"]["exit"], "fail")

    def test_a_non_repeatable_unit_escalates_to_the_ten_pair_stage(self):
        self.prepared()
        self.once("graph", "cand", lambda run: grow(run, "fragment", 100))
        a, first = self.decide()
        self.assertTrue(first["success"], first.get("failure"))
        r = first["outcome"]["results"]["S1:fragment"]
        self.assertEqual((r["decision"], r["owed"]),
                         ("inconclusive", "extend"))
        self.assertEqual(first["outcome"]["owed"], [["extend", "graph"]])
        self.assertEqual(st.exit_of(first), 2)
        ext = self.args("second", storage_counts=a.storage_counts,
                        timing_counts=a.timing_counts,
                        first=Path(first["output"]))
        spec = st.extend_spec(ext)
        self.assertEqual(spec["names"], ["graph"])
        report = st.run(ext, spec)
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(len(report["runs"]), 20)
        row = report["outcome"]["results"]["S1:fragment"]
        self.assertEqual((row["decision"], row["mode"]), ("pass",
                                                          "paired"))
        chain = st.replay_chain(report["output"], counts=a.storage_counts)
        self.assertEqual([e["stage"] for e in chain], ["run", "extend"])
        final = st.final_rows(chain)
        self.assertEqual(final["S1:fragment"]["stage"], "extend")
        self.assertEqual(final["L1:state-empty"]["stage"], "run")
        self.assertEqual(st.owed_units(chain, "extend"), [])

    def test_the_extend_stage_refuses_when_nothing_is_owed(self):
        a, first = self.go()
        ext = self.args("second", storage_counts=a.storage_counts,
                        timing_counts=a.timing_counts,
                        first=Path(first["output"]))
        with self.assertRaisesRegex(dw.Refusal, "owed"):
            st.extend_spec(ext)

    def noop_leak(self, run):
        i = rt.find(run, "live", phase="noop.before")
        j = rt.find(run, "release", release="noop")
        m = run[rt.find(run, "probe")]["params"]["m"]
        run[i:j + 1] = rt.release_rows("release", "release", ("noop",), m,
                                       1)
        return run

    def test_an_unresolved_floor_is_followed_up_at_a_larger_m(self):
        self.prepared()
        self.world.edits["release", "cand"] = self.noop_leak
        a, first = self.decide()
        self.assertTrue(first["success"], first.get("failure"))
        rows = first["outcome"]["results"]
        self.assertEqual(rows["R1:simpset"]["decision"], "inconclusive")
        self.assertEqual(rows["R1:simpset"]["owed"], "followup")
        self.assertEqual(first["outcome"]["owed"], [["followup",
                                                      "release"]])
        self.world.edits.clear()
        pre = self.args("pre2", storage_counts=a.storage_counts,
                        timing_counts=a.timing_counts,
                        stage=Path(first["output"]))
        data = st.predeclare_followup(pre)
        self.assertEqual(data["followup"]["m"], M * st.FOLLOWUP_FACTOR)
        self.assertEqual(data["workloads"], ["release"])
        out = self.world.repo / "src/simp/tests/performance/" \
            "task33_storage_followup_counts.json"
        out.write_text(dw.dumps(data))
        self.commit(out)
        fu = self.args("third", storage_counts=a.storage_counts,
                       followup_counts=out, timing_counts=a.timing_counts,
                       stage=Path(first["output"]))
        report = st.run(fu, st.followup_spec(fu))
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(report["params"]["m"], M * st.FOLLOWUP_FACTOR)
        self.assertEqual(report["outcome"]["results"]["R1:simpset"][
            "decision"], "pass")
        chain = st.replay_chain(report["output"], counts=a.storage_counts,
                                followup_counts=out)
        self.assertEqual([e["stage"] for e in chain], ["run", "followup"])
        self.assertEqual(st.final_rows(chain)["R1:simpset"]["stage"],
                         "followup")
        self.assertEqual(st.owed_units(chain, "followup"), [])


def incomparable(run):
    """A release run whose readings of one kind differ in gc_share."""
    i = rt.find(run, "live", phase="simpset.held")
    return rt.edit(run, i, gc_share=1)


class Redraws(Chain34):
    def test_a_not_comparable_process_is_redrawn(self):
        self.once("release", "cand", incomparable)
        args, report = self.run_stage("smoke", "smoke")
        self.assertTrue(report["success"], report.get("failure"))
        runs = [e for e in report["runs"] if e["workload"] == "release"
                and e["side"] == "cand"]
        self.assertEqual([(e["redraw"], e["accepted"]) for e in runs],
                         [(0, False), (1, True)])
        self.assertTrue(runs[1]["receipt"].endswith("-r1.json.gz"))
        folder = Path(report["output"])
        info = st.replay_chain(folder)[-1]["info"]
        self.assertEqual(info["replayed"], len(report["runs"]))

    def test_a_process_that_never_compares_is_a_refusal(self):
        self.world.edits["release", "cand"] = incomparable
        args, report = self.run_stage("smoke", "smoke")
        self.assertFalse(report["success"])
        self.assertIn("process rejected", report["failure"])
        self.assertEqual(len([e for e in report["runs"]
                              if e["workload"] == "release" and
                              e["side"] == "cand"]), st.MAX_REDRAWS + 1)

    def test_a_malformed_process_is_not_redrawn(self):
        self.once("release", "cand", lambda run: run[:-1])
        args, report = self.run_stage("smoke", "smoke")
        self.assertFalse(report["success"])
        self.assertEqual(len([e for e in report["runs"]
                              if e["workload"] == "release"]), 2)

    def test_unequal_lengths_of_roots_or_probe_directories_refuse(self):
        report = dict(roots=dict(base="/a/base", cand="/a/cand"),
                      reporter=dict(base=dict(dir="/p/base"),
                                    cand=dict(dir="/p/cand")))
        st.check_lengths(report)
        for key, value in (("roots", dict(base="/a/base",
                                          cand="/a/cands")),
                           ("reporter", dict(base=dict(dir="/p/base"),
                                             cand=dict(dir="/p/c")))):
            with self.assertRaisesRegex(dw.Refusal, "length"):
                st.check_lengths(dict(report, **{key: value}))


def inert(run):
    """A graph run that announces the control switch but does nothing."""
    plain = rt.graph_run(run[0]["params"]["sizes"])
    return [rt.head("graph", "graph", run[0]["params"],
                    graph_extra=True)] + plain[1:]


class Controls34(Chain34):
    def pilot(self, name="pilot", m0=M):
        return self.stage(name, "pilot", sizes=SIZES, m0=m0)[1]

    def test_every_control_is_detected_at_the_decision_configuration(self):
        _, smoke = self.stage("smoke", "smoke")
        pilot = self.pilot()
        _, control = self.stage("control", "control",
                                pilot=self.world.tmp / "pilot")
        found = control["outcome"]["controls"]
        self.assertEqual(sorted(found), ["ext_ordinary", "graph_extra",
                                         "hook", "leak"])
        self.assertTrue(all(c["detected"] for c in found.values()), found)
        self.assertEqual(control["params"], st.decision_params(pilot))
        self.assertEqual(st.exit_of(control), 0)
        self.assertEqual(control["outcome"]["negative_control"]["decision"],
                         "fail")

    def test_the_ordinary_process_with_the_extension_is_refused(self):
        self.stage("smoke", "smoke")
        self.pilot()
        _, control = self.stage("control", "control",
                                pilot=self.world.tmp / "pilot")
        last = control["runs"][-1]
        self.assertEqual((last["workload"], last["side"], last["accepted"]),
                         (st.ORDINARY, "cand", False))

    def test_an_undetected_control_is_not_a_negative_control(self):
        self.stage("smoke", "smoke")
        self.pilot()
        self.world.edits["graph+graph_extra", "base"] = inert
        _, control = self.stage("control", "control",
                                pilot=self.world.tmp / "pilot")
        self.assertFalse(control["outcome"]["controls"]["graph_extra"][
            "detected"])
        self.assertFalse(control["outcome"]["negative_control"]["detected"])
        self.assertEqual(st.exit_of(control), 1)
        self.timing_counts()
        args = self.args("pre", timing_counts=self.world.repo / "src/simp/"
                         "tests/performance/task33_counts.json",
                         smoke=self.world.tmp / "smoke",
                         pilot=self.world.tmp / "pilot",
                         control=self.world.tmp / "control", offline=[])
        with self.assertRaisesRegex(dw.Refusal, "control was not "
                                    "detected.*graph_extra"):
            st.predeclare_run(args)

    def test_controls_off_the_decision_configuration_are_refused(self):
        self.stage("smoke", "smoke")
        self.pilot()
        self.pilot("pilot2", 2 * M)
        _, control = self.stage("control", "control",
                                pilot=self.world.tmp / "pilot2")
        self.timing_counts()
        args = self.args("pre", timing_counts=self.world.repo / "src/simp/"
                         "tests/performance/task33_counts.json",
                         smoke=self.world.tmp / "smoke",
                         pilot=self.world.tmp / "pilot",
                         control=self.world.tmp / "control", offline=[])
        with self.assertRaisesRegex(dw.Refusal, "decision configuration"):
            st.predeclare_run(args)

    def test_a_pilot_over_the_cap_is_not_usable(self):
        self.stage("smoke", "smoke")
        noisy = lambda run: self.world_noise(run)
        self.world.edits["release", "base"] = noisy
        pilot = self.pilot()
        out = pilot["outcome"]
        self.assertFalse(out["covered"])
        self.assertTrue(out["capped"])
        self.assertGreater(out["required_m"], st.M_CAP)
        self.assertEqual(out["m"], st.M_CAP)
        self.assertEqual(st.exit_of(pilot), 2)
        with self.assertRaisesRegex(dw.Refusal, "over the cap"):
            st.info_spec(self.args("c", pilot=self.world.tmp / "pilot"),
                         "control")

    def world_noise(self, run):
        """A release run whose no-op floor moves by a million words."""
        i = rt.find(run, "live", phase="noop.before")
        j = rt.find(run, "release", release="noop")
        m = run[rt.find(run, "probe")]["params"]["m"]
        self.noise = getattr(self, "noise", 0) + 10 ** 6
        run[i:j + 1] = rt.release_rows("release", "release", ("noop",), m,
                                       self.noise // m)
        return run

    def test_the_pilot_records_noise_and_the_clamped_m(self):
        pilot = self.pilot()
        out = pilot["outcome"]
        self.assertTrue(out["covered"])
        self.assertEqual(out["m"], M)
        self.assertEqual(out["required_m"], M)
        self.assertFalse(out["capped"])
        self.assertTrue(all(all(v.values()) for v in
                            [out["graph_repeatable"]]))


FAKE_AUDIT = """\
import argparse, hashlib, json, sys
from pathlib import Path
p = argparse.ArgumentParser()
p.add_argument("--output", required=True)
out = Path(p.parse_args().output) / "20260101T000000"
out.mkdir(parents=True)
cases = []
for i in range(%(cases)d):
    log = out / ("case%%d.log" %% i)
    log.write_text("OBS result=pass\\n")
    data = log.read_bytes()
    cases.append(dict(order=i, foreign_kind="k", foreign_owner="o",
                      **{"pass": %(ok)s}, log=log.name, log_seal=dict(
                          bytes=len(data),
                          sha256=hashlib.sha256(data).hexdigest())))
(out / "receipt.json").write_text(json.dumps(dict(
    **{"pass": True}, head="%(head)s", cases=cases)))
"""


class Audit(Chain34):
    def install(self, cases=8, ok="True", head=None):
        w = self.world
        script = w.roots["cand"] / "src/simp/tests/api-audit/run.py"
        script.parent.mkdir(parents=True)
        script.write_text(FAKE_AUDIT % dict(
            cases=cases, ok=ok, head=head or w.cand_pin))

    def audit(self):
        self.prepared()
        a = self.args("audit", storage_counts=self.predeclare_done[2],
                      timing_counts=self.predeclare_done[0].timing_counts)
        return a, st.run(a, st.audit_spec(a))

    def test_eight_passes_with_a_sealed_receipt_pass_e1_and_l3(self):
        self.install()
        a, report = self.audit()
        self.assertTrue(report["success"], report.get("failure"))
        rows = report["outcome"]["results"]
        self.assertEqual(sorted(rows), ["E1:api-audit", "L3:api-audit"])
        self.assertTrue(all(r["decision"] == "pass" for r in rows.values()))
        self.assertEqual(rows["E1:api-audit"]["cases"], 8)
        self.assertEqual(st.exit_of(report), 0)
        last = st.replay_chain(report["output"],
                               counts=a.storage_counts)[-1]
        self.assertEqual(last["info"]["exit"], "pass")
        receipt = Path(report["output"]) / report["audit"]["receipt"]
        receipt.write_text(receipt.read_text() + " ")
        with self.assertRaises(dw.Refusal):
            st.replay_chain(report["output"], counts=a.storage_counts)

    def test_fewer_than_eight_cases_or_a_failed_case_fails(self):
        for kwargs, why in ((dict(cases=7), "7 cases"),
                            (dict(ok="False"), "not PASS")):
            with self.subTest(why):
                self.setUp()
                self.install(**kwargs)
                a, report = self.audit()
                self.assertTrue(report["success"], report.get("failure"))
                row = report["outcome"]["results"]["E1:api-audit"]
                self.assertEqual(row["decision"], "fail")
                self.assertIn(why, row["reason"])
                self.assertEqual(st.exit_of(report), 1)

    def test_the_audit_must_be_of_the_candidates_head(self):
        self.install(head="2" * 40)
        a, report = self.audit()
        row = report["outcome"]["results"]["E1:api-audit"]
        self.assertEqual(row["decision"], "fail")
        self.assertIn("not the candidate", row["reason"])


class FakeTree:
    """A fake `.agent-files` of a repository with the two snapshots, their
    HOMEs and sequence copies as the snapshot driver lays them out, a
    sealed harvest and a sealed api-audit stage."""

    def __init__(self, tmp):
        self.tmp = Path(tmp)
        self.repo = self.tmp / "repo"
        self.repo.mkdir()
        t32.git(self.repo, "init", "-q")
        self.agent = self.repo / ".agent-files"
        self.snaps = self.agent / "snapshots/task32"
        self.scratch = self.agent / "scratch/task32"
        self.scratch_root = self.tmp / "t33"
        self.evidence = self.agent / "evidence/task33"
        self.sides = {}
        for label in ("base", "cand"):
            root = self.snaps / label
            (root / "bin").mkdir(parents=True)
            (root / "bin/hol").write_text("x" * 100)
            home = self.scratch / ("home-%s-a0" % label)
            home.mkdir(parents=True)
            (home / "f").write_text("home")
            seq = "%064x" % (1 if label == "base" else 2)
            copy_ = self.scratch / ("task32-%s.seq" % seq)
            copy_.write_text(label)
            self.sides[label] = dict(
                root=str(root), home=str(home), scratch=str(self.scratch),
                sequence=dict(path=str(copy_), sha256=seq),
                pin=label[0] * 40, tree=label[0] * 40)
        self.scratch_root.mkdir()
        (self.scratch_root / "run").write_text("x")
        self.manifest = self.agent / "evidence/task32/snapshots.json"
        self.manifest.parent.mkdir(parents=True)
        self.manifest.write_text(dw.dumps(dict(
            schema=dw.snap.SCHEMA, sides=self.sides)))
        self.evidence.mkdir(parents=True)
        self.harvest()
        self.audit()

    def harvest(self, **change):
        path = self.evidence / "harvest.json"
        path.write_text(dw.dumps(dict(dict(
            schema=offline.SCHEMA, command="harvest", success=True),
            **change)))
        Path(str(path) + ".seal").write_text(dw.dumps(acc.seal(path)))

    def audit(self, ok=True):
        folder = self.evidence / "audit"
        (folder / "api-audit/20260101").mkdir(parents=True, exist_ok=True)
        receipt = folder / "api-audit/20260101/receipt.json"
        receipt.write_text(json.dumps({"pass": ok}))
        (folder / "downstream.json").write_text(dw.dumps(dict(
            schema=st.SCHEMA, mode="audit", success=True, audit=dict(
                receipt="api-audit/20260101/receipt.json",
                receipt_seal=acc.seal(receipt)))))

    def args(self, **extra):
        values = dict(evidence=self.evidence, manifest=self.manifest,
                      repo=self.repo, scratch_root=self.scratch_root,
                      verify_argv=[sys.executable, "-c", "pass"])
        values.update(extra)
        return argparse.Namespace(**values)

    def listed(self):
        out = [self.scratch_root]
        for v in self.sides.values():
            out += [Path(v["root"]), Path(v["home"]),
                    Path(v["sequence"]["path"])]
        return out


class DisposeSnapshots(unittest.TestCase):
    def setUp(self):
        self.dir = t32.tempfile.TemporaryDirectory(prefix="t33d-test-")
        self.addCleanup(self.dir.cleanup)
        self.tree = FakeTree(self.dir.name)

    def refused(self, pattern, **extra):
        with self.assertRaisesRegex(dw.Refusal, pattern):
            dispose.dispose_snapshots(self.tree.args(**extra))
        for path in self.tree.listed():
            self.assertTrue(path.exists(), path)
        self.assertFalse(
            (self.tree.evidence / "snapshot-disposal.json").exists())

    def test_the_listed_paths_are_removed_and_the_rest_kept(self):
        t = self.tree
        other = t.snaps / "other"
        other.mkdir()
        (t.scratch / "unrelated.txt").write_text("keep")
        listed = t.listed()
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(dispose.dispose_snapshots(t.args()), 0)
        for path in listed:
            self.assertFalse(path.exists(), path)
        self.assertTrue(other.is_dir())
        self.assertTrue((t.scratch / "unrelated.txt").is_file())
        data = json.loads((t.evidence / "snapshot-disposal.json"
                           ).read_text())
        self.assertEqual(data["schema"], dispose.DISPOSAL_SCHEMA)
        self.assertEqual(sorted(data["removed"]),
                         sorted(str(p) for p in listed))
        self.assertEqual(data["verify"]["exit"], 0)
        self.assertEqual(data["manifest"]["seal"], acc.seal(t.manifest))
        self.assertEqual(data["api_audit"]["receipt_seal"],
                         acc.seal(Path(data["api_audit"]["receipt"])))
        self.assertTrue(all(v > 0 for k, v in data["sizes_bytes"].items()
                            if not k.endswith(".seq") and
                            "t33" not in k))
        self.assertTrue(t.manifest.is_file())
        self.assertTrue(t.evidence.is_dir())

    def test_empty_parents_go_and_the_agent_directory_stays(self):
        t = self.tree
        with contextlib.redirect_stdout(io.StringIO()):
            dispose.dispose_snapshots(t.args())
        self.assertFalse(t.snaps.exists())
        self.assertFalse(t.scratch.exists())
        self.assertTrue(t.agent.is_dir())

    def test_a_second_disposal_is_refused(self):
        with contextlib.redirect_stdout(io.StringIO()):
            dispose.dispose_snapshots(self.tree.args())
        with self.assertRaisesRegex(dw.Refusal, "disposed"):
            dispose.dispose_snapshots(self.tree.args())

    def test_no_harvest_or_an_unsealed_one_refuses_and_removes_nothing(self):
        t = self.tree
        t.harvest(extra=1)
        Path(str(t.evidence / "harvest.json") + ".seal").write_text(
            dw.dumps(dict(sha256="0" * 64, bytes=1)))
        self.refused("harvest seal")
        (t.evidence / "harvest.json").unlink()
        self.refused("0 harvest reports")

    def test_a_failed_harvest_refuses(self):
        self.tree.harvest(success=False)
        self.refused("not a successful offline report")

    def test_the_audit_receipt_must_be_the_sealed_pass(self):
        t = self.tree
        t.audit(ok=False)
        self.refused("not a pass")
        t.audit()
        receipt = t.evidence / "audit/api-audit/20260101/receipt.json"
        receipt.write_text(json.dumps({"pass": True, "x": 1}))
        self.refused("not the sealed one")
        shutil.rmtree(t.evidence / "audit")
        self.refused("0 successful api-audit")

    def test_a_failing_verification_removes_nothing(self):
        self.refused("verif|failed", verify_argv=[sys.executable, "-c",
                                                   "raise SystemExit(1)"])

    def test_a_missing_snapshot_refuses_without_removing_the_others(self):
        t = self.tree
        shutil.rmtree(t.sides["cand"]["root"])
        with self.assertRaisesRegex(dw.Refusal, "absent"):
            dispose.dispose_snapshots(t.args())
        self.assertTrue(Path(t.sides["base"]["root"]).exists())
        self.assertTrue(t.scratch_root.exists())

    def test_a_path_outside_the_snapshot_layout_is_refused(self):
        t = self.tree
        side = dict(t.sides["cand"], root=str(t.tmp / "elsewhere"))
        (t.tmp / "elsewhere").mkdir()
        t.manifest.write_text(dw.dumps(dict(
            schema=dw.snap.SCHEMA, sides=dict(t.sides, cand=side))))
        with self.assertRaisesRegex(dw.Refusal, "not below"):
            dispose.dispose_snapshots(t.args())
        self.assertTrue((t.tmp / "elsewhere").exists())

    def test_a_symbolic_link_is_refused(self):
        t = self.tree
        home = Path(t.sides["base"]["home"])
        shutil.rmtree(home)
        target = t.tmp / "target"
        target.mkdir()
        home.symlink_to(target)
        with self.assertRaisesRegex(dw.Refusal, "symbolic link|canonical"):
            dispose.dispose_snapshots(t.args())
        self.assertTrue(target.exists())

    def test_a_scratch_root_not_named_t33_is_refused(self):
        t = self.tree
        other = t.tmp / "precious"
        other.mkdir()
        self.refused("t33 directory", scratch_root=other)
        self.assertTrue(other.exists())


def offline_report(command, checks, **data):
    return dict(schema=offline.SCHEMA, command=command, success=True,
                checks=checks, data=data, code={})


def check_of(ident, case, status="pass"):
    return dict(id=ident, case=case, status=status, reason=ident)


class Joining(unittest.TestCase):
    def test_timing_rows_become_l4_decisions(self):
        disp = dict(workloads={
            "load-simpLib": dict(status="pass", note=None,
                                 stages=[dict(stage="first")]),
            "first-use": dict(status="followup", note="borderline",
                              stages=[dict(stage="first"),
                                      dict(stage="second")])})
        got = dispose.timing_decisions(None, disp)
        self.assertEqual([(x["case"], x["kind"], x["decision"],
                           x["source"]) for x in got], [
            ("L4", "first-use", "inconclusive", "timing:second"),
            ("L4", "load-simpLib", "pass", "timing:first")])

    def test_offline_checks_of_combined_cases_are_decided_in_each(self):
        found = {"audit": (offline_report("audit", [
            check_of("c1", "L1/S3"), check_of("c2", "L2", "fail"),
            check_of("c3", "S3", "skipped")]), dict(seal=1)),
            "archive": (offline_report("archive", [], above=[
                dict(unit="a", wholly_above_margin=True),
                dict(unit="b", wholly_above_margin=False)]),
                dict(seal=2))}
        got, attribution = dispose.offline_decisions(found)
        self.assertEqual(
            sorted((x["case"], x["kind"], x["decision"]) for x in got
                   if x["source"] == "offline:audit"),
            [("L1", "c1", "pass"), ("L2", "c2", "fail"),
             ("S3", "c1", "pass"), ("S3", "c3", "inconclusive")])
        self.assertEqual([x["unit"] for x in attribution], ["a"])
        missing = [x for x in got if x["case"] == "offline"]
        self.assertEqual([(x["kind"], x["decision"]) for x in missing],
                         [("harvest", "blocked")])

    def test_overall_is_the_worst_gate(self):
        self.assertEqual(dispose.overall(["pass", "pass"]), "pass")
        self.assertEqual(dispose.overall(["pass", "inconclusive"]),
                         "inconclusive")
        self.assertEqual(dispose.overall(["inconclusive", "blocked",
                                          "fail"]), "fail")
        self.assertEqual(dispose.overall(["pass", "blocked"]), "blocked")

    def test_the_expected_storage_cases_are_one_per_case_and_kind(self):
        keys = dispose.expected_storage()
        self.assertEqual(len(keys), len(set(keys)))
        self.assertIn(("E1", "api-audit"), keys)
        self.assertIn(("S2", "first-use"), keys)
        self.assertIn(("R1", "weak"), keys)


class Disposition(Chain34):
    install = Audit.install

    def stages(self):
        self.prepared()
        a, first = self.decide()
        self.assertTrue(first["success"], first.get("failure"))
        self.install()
        au = self.args("audit", storage_counts=a.storage_counts,
                       timing_counts=a.timing_counts)
        audit = st.run(au, st.audit_spec(au))
        self.assertTrue(audit["success"], audit.get("failure"))
        return a, first, audit

    def offline_files(self, checks=None):
        out = []
        for command in ("archive", "audit", "harvest"):
            path = self.world.tmp / ("%s.json" % command)
            path.write_text(dw.dumps(offline_report(
                command, [check_of(command + "-ok", "S3")] if checks is
                None else checks, above=[])))
            Path(str(path) + ".seal").write_text(dw.dumps(acc.seal(path)))
            out.append(path)
        return out

    def dispose(self, stages, a, first, out="disposition.json", **extra):
        w = self.world
        timing = [dict(report=dict(
            repo=str(w.repo), base=first["base"], cand=first["cand"],
            key=first["key"], manifest=first["manifest"]), stage="first")]
        disp = dict(workloads={"load-simpLib": dict(
            status="pass", note="", stages=[dict(stage="first")])})
        args = argparse.Namespace(**dict(dict(
            stage=[Path(r["output"]) for r in stages],
            timing_stage=w.tmp / "timing", offline=self.offline_files(),
            repo=w.repo, ledger=None, timing_counts=None,
            storage_counts=a.storage_counts, followup_counts=None,
            relocated=[], out=w.tmp / out), **extra))
        with mock.patch.object(dw, "replay_chain", lambda *x: timing), \
                mock.patch.object(dw, "disposition",
                                  lambda *x: disp), \
                mock.patch.object(offline, "check_code", lambda c: None), \
                contextlib.redirect_stdout(io.StringIO()):
            return dispose.dispose(args), args.out

    def test_the_disposition_joins_timing_storage_and_offline(self):
        a, first, audit = self.stages()
        code, out = self.dispose([first, audit], a, first)
        data = json.loads(out.read_text())
        self.assertEqual(code, 0, data["counts"])
        self.assertEqual(data["status"], "pass")
        keys = [(x["case"], x["kind"]) for x in data["decisions"]]
        self.assertEqual(len(keys), len(set(keys)))
        for key in dispose.expected_storage():
            self.assertIn(key, keys)
        self.assertIn(("L4", "load-simpLib"), keys)
        self.assertEqual(sorted(data["offline"]),
                         ["archive", "audit", "harvest"])
        self.assertEqual(len(data["storage_chains"]), 2)
        self.assertEqual(data["ledgers"]["storage"]["attempts"][-1][
            "statuses"], ["pass"])
        self.assertEqual(data["code"], dw.code_seals())

    def test_a_missing_audit_stage_blocks_its_cases(self):
        a, first, audit = self.stages()
        code, out = self.dispose([first], a, first)
        data = json.loads(out.read_text())
        self.assertEqual((code, data["status"]), (2, "blocked"))
        blocked = {(x["case"], x["kind"]) for x in data["decisions"]
                   if x["decision"] == "blocked"}
        self.assertEqual(blocked, {("E1", "api-audit"),
                                   ("L3", "api-audit")})

    def test_a_failing_decision_fails_the_disposition(self):
        self.prepared()
        self.world.edits["graph", "cand"] = lambda run: grow(
            run, "fragment", 100)
        a, first = self.decide()
        code, out = self.dispose([first], a, first)
        data = json.loads(out.read_text())
        self.assertEqual((code, data["status"]), (1, "fail"))
        got = {(x["case"], x["kind"]): x["decision"]
               for x in data["decisions"]}
        self.assertEqual(got[("S1", "fragment")], "fail")
        self.assertEqual(got[("S1", "merge")], "pass")

    def test_an_offline_report_with_a_changed_seal_is_refused(self):
        a, first, audit = self.stages()
        files = self.offline_files()
        files[0].write_text(files[0].read_text() + " ")
        with mock.patch.object(Disposition, "offline_files",
                               lambda self: files):
            with self.assertRaisesRegex(dw.Refusal, "seal"):
                self.dispose([first, audit], a, first)

    def test_the_disposition_is_never_overwritten(self):
        a, first, audit = self.stages()
        self.dispose([first, audit], a, first)
        with self.assertRaises(FileExistsError):
            self.dispose([first, audit], a, first)


class Cli(Chain34):
    COMMON = ["--repo", "r", "--base-root", "b", "--cand-root", "c",
              "--manifest", "m"]

    def code(self, argv):
        out = io.StringIO()
        with contextlib.redirect_stderr(out), \
                contextlib.redirect_stdout(out):
            try:
                return st.main(argv), out.getvalue()
            except SystemExit as stop:
                return stop.code, out.getvalue()

    def test_usage_errors_exit_3(self):
        for argv in ([], ["bogus"], ["smoke"],
                     ["smoke"] + self.COMMON,  # no --output
                     ["smoke", "--output", "o"] + self.COMMON + [
                         "--sizes", "3,1"],
                     ["run", "--output", "o"] + self.COMMON + [
                         "--only", "graph"],
                     ["extend", "--output", "o"] + self.COMMON,
                     ["predeclare"] + self.COMMON,
                     ["replay"], ["dispose"],
                     ["dispose-snapshots"]):
            with self.subTest(argv=argv):
                self.assertEqual(self.code(argv)[0], 3)

    def test_a_refused_stage_exits_3_with_the_reason(self):
        w = self.world
        code, text = self.code([
            "smoke", "--repo", str(w.repo), "--base-root",
            str(w.roots["base"]), "--cand-root", str(w.roots["cand"]),
            "--manifest", str(w.tmp / "nonesuch.json"), "--output",
            str(w.tmp / "o")])
        self.assertEqual(code, 3, text)

    def test_the_commands_are_the_stages_and_the_closing_ones(self):
        self.assertEqual(
            st.COMMANDS, ("smoke", "pilot", "control", "run", "extend",
                          "followup", "audit", "predeclare", "replay",
                          "dispose", "dispose-snapshots"))
        parser = st.build_parser()
        got = parser.parse_args(["smoke", "--output", "o"] + self.COMMON)
        self.assertEqual(got.command, "smoke")
        self.assertFalse(got.authorize_measurements)

    def test_the_exit_codes_follow_the_stage_status(self):
        base = dict(success=True, mode="run", stage="run")
        out = lambda s: dict(results={"x": dict(decision=s, owed=None)})
        for status, code in (("pass", 0), ("fail", 1),
                             ("inconclusive", 2), ("blocked", 2)):
            self.assertEqual(st.exit_of(dict(base, outcome=out(status))),
                             code)
        self.assertEqual(st.exit_of(dict(success=False, mode="run")), 3)
        self.assertEqual(st.exit_of(dict(success=False, mode="run",
                                         blocked="x")), 2)

    def test_a_decision_stage_refuses_without_the_committed_counts(self):
        self.info_stages()
        counts = self.timing_counts()
        args = self.args("pre", timing_counts=counts,
                         smoke=self.world.tmp / "smoke",
                         pilot=self.world.tmp / "pilot",
                         control=self.world.tmp / "control", offline=[])
        data = st.predeclare_run(args)
        out = self.world.repo / "src/simp/tests/performance/counts.json"
        out.write_text(dw.dumps(data))  # written, not committed
        run = self.args("first", timing_counts=counts, storage_counts=out)
        with self.assertRaisesRegex(dw.Refusal, "not committed"):
            st.run_spec(run)

    def test_predeclare_refuses_uncommitted_timing_counts(self):
        self.info_stages()
        counts = self.timing_counts()
        counts.write_text(counts.read_text() + " ")
        args = self.args("pre", timing_counts=counts,
                         smoke=self.world.tmp / "smoke",
                         pilot=self.world.tmp / "pilot",
                         control=self.world.tmp / "control", offline=[])
        with self.assertRaisesRegex(dw.Refusal, "committed"):
            st.predeclare_run(args)

    def test_m_is_clamped_with_required_and_capped(self):
        self.info_stages()
        pilot = Path(self.world.tmp / "pilot")
        report = json.loads((pilot / "downstream.json").read_text())
        self.assertEqual(
            (report["outcome"]["m"], report["outcome"]["required_m"],
             report["outcome"]["capped"]), (M, M, False))
        _, data, out = self.predeclare()
        self.assertEqual((data["required_m"], data["m_cap"],
                          data["capped"]), (M, st.M_CAP, False))
        self.assertEqual(data["timing_counts"]["seal"], acc.seal(
            self.world.repo / "src/simp/tests/performance/"
            "task33_counts.json"))
        data["capped"] = True
        out.write_text(dw.dumps(data))
        with self.assertRaisesRegex(dw.Refusal, "disagree"):
            sides, mseal = dw.pins_of(self.args("x"))
            st.load_storage_counts(out, sides, "run", self.world.repo,
                                   mseal, committed=False)


class Interfaces(Chain34):
    def test_an_anchor_moved_on_a_baseline_process_is_a_refusal(self):
        real = st.summarize

        def moved(receipt, unit, root):
            out = real(receipt, unit, root)
            if unit["name"] == "graph":
                out["anchor_moved"] = [dict(kind="fragment", n=100)]
            return out
        with mock.patch.object(st, "summarize", moved):
            args, report = self.run_stage("smoke", "smoke")
        self.assertFalse(report["success"])
        self.assertIn("anchor moved", report["failure"])

    def test_the_information_runs_of_the_ledger_carry_the_control(self):
        self.info_stages()
        state, found = dw.read_ledger(self.world.ledger(),
                                      st.LEDGER_TABLE)
        runs = dw.info_runs(state, {}, st.LEDGER_TABLE)
        self.assertEqual([r["mode"] for r in runs],
                         ["smoke", "pilot", "control"])
        self.assertEqual((runs[2]["decision"], runs[2]["detected"]),
                         ("fail", True))
        self.assertTrue(all(r["status"] == "success" for r in runs))

    def test_the_storage_and_loading_tables_share_the_ledger_file(self):
        self.info_stages()
        state, found = dw.read_ledger(self.world.ledger(), dw.TABLE)
        self.assertEqual(found, {})
        self.assertEqual(dw.TABLE, "task33-loading")
        self.assertEqual(st.LEDGER_TABLE, "task33-storage")
