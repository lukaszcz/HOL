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
            return ext_records(m, sizes)
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
        if self.fault and self.fault(name, side, self.counter) == "stray":
            (Path(cwd) / "stray.txt").write_text("x")
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
            followup_counts=None, timing_followup_counts=None,
            storage_followup_counts=None)
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

    def test_as_built_rows_are_judged_on_the_sizes_kept_in_every_process(
            self):
        def covered(*sizes):
            run = summ(graph_of())
            return dict(run, gateable_coverage=dict(
                run["gateable_coverage"], fragment=list(sizes)))
        full = covered(0, 1, 100)
        # a size left out of one process leaves it out of the comparison
        r = rules.s1_kind([full] * 3, [full, full, covered(0, 100)],
                          "fragment")
        self.assertEqual(r["decision"], "pass", r["reason"])
        self.assertEqual(r["as_built_kept"], [0, 100])
        self.assertTrue(r["as_built_gated"])
        self.assertNotIn("size 1", r["as_built"])
        # the kept sizes need one of at least 100
        r = rules.s1_kind([full] * 3, [full, full, covered(0, 1)],
                          "fragment")
        self.assertEqual(r["decision"], "inconclusive", r["reason"])
        self.assertFalse(r["as_built_gated"])
        self.assertEqual(r["as_built_kept"], [0, 1])

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

    def test_a_small_held_object_is_blocked_not_followed_up(self):
        run = release_of()
        c = [dict(run, held=dict(run["held"], simpset=Fraction(5)))] * 3
        r = rules.r1_kind([run] * 3, c, "simpset")
        self.assertEqual((r["decision"], r["owed"]), ("blocked", None))
        self.assertIn("20", r["reason"])
        self.assertIn("cand", r["reason"])
        r = rules.r1_kind(c, [run] * 3, "simpset")
        self.assertEqual((r["decision"], r["owed"]), ("blocked", None))
        self.assertIn("base", r["reason"])

    def test_held_readings_not_comparable_are_left_out(self):
        run = release_of()
        mark = lambda ok: dict(run, held_comparable=dict(
            run["held_comparable"], simpset=ok))
        small = dict(mark(False), held=dict(run["held"],
                                            simpset=Fraction(5)))
        r = rules.r1_kind([run] * 2 + [small], [run] * 3, "simpset")
        self.assertEqual(r["decision"], "pass", r["reason"])
        r = rules.r1_kind([small] * 3, [run] * 3, "simpset")
        self.assertEqual((r["decision"], r["owed"]), ("blocked", None))
        self.assertIn("no comparable held", r["reason"])

    def test_a_process_with_a_retained_half_word_fails_whatever_the_median(
            self):
        run = release_of()
        keep = lambda x: dict(run, residual=dict(run["residual"],
                                                 simpset=Fraction(x)))
        c = [run, run, keep(Fraction(1, 2))]
        r = rules.r1_kind([run] * 3, c, "simpset")
        self.assertEqual(r["decision"], "fail", r["reason"])
        c = [run, run, keep(Fraction(49, 100))]
        self.assertEqual(rules.r1_kind([run] * 3, c, "simpset")["decision"],
                         "inconclusive")  # under 1/2 but not stable

    def test_residuals_compare_as_exact_fractions(self):
        run = release_of()
        keep = lambda x: dict(run, residual=dict(run["residual"],
                                                 simpset=x))
        almost = Fraction(1, 2) - Fraction(1, 10 ** 9)
        r = rules.r1_kind([run] * 3, [keep(almost)] * 3, "simpset")
        self.assertEqual(r["decision"], "pass", r["reason"])
        r = rules.r1_kind([run] * 3, [keep(Fraction(1, 2))] * 3, "simpset")
        self.assertEqual(r["decision"], "fail", r["reason"])

    def test_a_baseline_weak_probe_not_collected_blocks(self):
        run = release_of()
        lost = dict(run, weak=dict(run["weak"], status="fail"))
        r = rules.weak_row([lost] * 3, [run] * 3)
        self.assertEqual(r["decision"], "blocked", r["reason"])
        self.assertEqual(rules.weak_row([run] * 3, [lost] * 3)["decision"],
                         "fail")

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

    def test_e2a_routes_like_s1(self):
        graph = [summ(graph_of())] * 3
        moved = [dict(ext_of(), anchor_moved=[dict(kind="fragment", n=100)]
                      )] * 3
        r = rules.e2a(moved, graph)
        self.assertEqual(r["decision"], "fail", r["reason"])
        jitter = [summ(graph_of()), summ(graph_of()),
                  summ(grow(graph_of(), "fragment", 100))]
        r = rules.e2a([ext_of()] * 3, jitter)
        self.assertEqual((r["decision"], r["owed"]),
                         ("inconclusive", "extend"), r["reason"])
        r = rules.e2a([ext_of()] * 10, [summ(graph_of())] * 10, paired=True)
        self.assertEqual((r["decision"], r["owed"]), ("pass", None),
                         r["reason"])
        gap = [dict(x, gateable={n: (dict(v, canonical=False) if n == 100
                                     else v)
                                 for n, v in x["gateable"].items()})
               for x in [summ(graph_of())] * 3]
        r = rules.e2a([ext_of()] * 3, gap)
        self.assertEqual((r["decision"], r["owed"]),
                         ("inconclusive", "extend"), r["reason"])

    def test_e2c_equal_lists_with_the_declared_additions_pass(self):
        plain = [registry_of()] * 3
        r = rules.e2c([ext_with()] * 3, plain, E2C)
        self.assertEqual(r["decision"], "pass", r["reason"])
        self.assertEqual(r["added"]["structures"], ["ExtA", "ExtB", "Probe"])
        self.assertEqual(r["added"]["listeners"], ["ext.onload"])

    def test_e2c_an_undeclared_addition_fails(self):
        plain = [registry_of()] * 3
        r = rules.e2c([ext_with(attributes=["userdef", "sneaky"])] * 3,
                      plain, E2C)
        self.assertEqual(r["decision"], "fail", r["reason"])
        self.assertEqual(r["undeclared"], dict(attributes=["sneaky"]))

    def test_e2c_a_missing_required_name_fails(self):
        plain = [registry_of()] * 3
        r = rules.e2c([ext_with(structures=["A", "B", "ExtA", "Probe"])] * 3,
                      plain, E2C)
        self.assertEqual(r["decision"], "fail", r["reason"])
        self.assertEqual(r["required_missing"], dict(structures=["ExtB"]))

    def test_e2c_a_declared_optional_name_may_be_absent_or_added(self):
        plain = [registry_of()] * 3
        r = rules.e2c([ext_with(attributes=["userdef", "opt"])] * 3, plain,
                      E2C)
        self.assertEqual(r["decision"], "pass", r["reason"])

    def test_e2c_prose_only_state_satisfies_nothing(self):
        plain = [registry_of()] * 3
        r = rules.e2c([ext_with(structures=[
            "A", "B", "ExtA", "ExtB", "Probe", "ProseState"])] * 3,
            plain, E2C)
        self.assertEqual(r["decision"], "fail", r["reason"])
        self.assertEqual(r["undeclared"], dict(structures=["ProseState"]))

    def test_e2c_a_removed_ordinary_entry_fails(self):
        plain = [registry_of()] * 3
        r = rules.e2c([ext_with(listeners=["ext.onload"])] * 3, plain, E2C)
        self.assertEqual(r["decision"], "fail", r["reason"])
        self.assertEqual(r["removed"], dict(listeners=["DB"]))

    def test_e2c_ordinary_listeners_keep_their_order(self):
        plain = [registry_of(listeners=["DB", "Other"])] * 3
        ext = [ext_with(listeners=["Other", "ext.onload", "DB"])] * 3
        r = rules.e2c(ext, plain, E2C)
        self.assertEqual(r["decision"], "fail", r["reason"])
        self.assertEqual(r["reordered"], ["listeners"])
        ext = [ext_with(listeners=["DB", "ext.onload", "Other"])] * 3
        self.assertEqual(rules.e2c(ext, plain, E2C)["decision"], "pass")

    def test_e2c_the_extension_processes_must_agree(self):
        plain = [registry_of()] * 3
        ext = [ext_with(), ext_with(), ext_with(structures=[
            "A", "B", "ExtA", "ExtB"])]
        r = rules.e2c(ext, plain, E2C)
        self.assertEqual(r["decision"], "fail", r["reason"])
        self.assertIn("disagree", r["reason"])

    def test_e2c_loaded_and_files_are_not_compared(self):
        plain = [registry_of()] * 3
        ext = [ext_with(loaded=["Abbrev", "simpLib", "simpExtLib"],
                        files=[["simpExtLib.uo", "/snap/sigobj"]])] * 3
        self.assertEqual(rules.e2c(ext, plain, E2C)["decision"], "pass")

    def test_the_committed_declaration_has_the_probe_support_registers(self):
        declared = offline.load_declared()["e2c"]
        self.assertEqual(offline.e2c_problems(declared), [])
        allowed, required = rules.declared_names(declared)
        self.assertIn("congLib", allowed["structures"])
        self.assertIn("simpExtLib", required["structures"])
        self.assertFalse(any("source" in n for names in allowed.values()
                             for n in names))

    def test_e2u_reports_the_closure_total_less_the_ordinary_one(self):
        base = ext_of()
        grown = dict(base["anchored"], total=[
            t + 9 for t in base["anchored"]["total"]])
        plain = [registry_of()] * 3
        ext = [dict(base, anchored=grown)] * 3
        r = rules.e2u(ext, plain)
        self.assertEqual((r["case"], r["kind"], r["decision"]),
                         ("E2", "u", "reported"))
        self.assertEqual(r["total"]["change"], 9)
        self.assertEqual(r["exclusive"]["simpLib"]["change"], 0)

    def test_e2u_without_a_total_is_reported_as_such(self):
        plain = [registry_of(missing=("Opening",))] * 3
        r = rules.e2u([ext_of()] * 3, plain)
        self.assertEqual(r["decision"], "reported")
        self.assertIn("no closure total", r["reason"])


E2C = dict(
    rule="r", probe_support=dict(
        justification="j", registers=dict(structures=["Probe"])),
    extension_state=[
        dict(name="ext", created_by="c", where="w", source="s",
             required=True, observable=True,
             registers=dict(structures=["ExtA", "ExtB"],
                            listeners=["ext.onload"])),
        dict(name="opt", created_by="c", where="w", source="s",
             required=False, observable=True,
             registers=dict(attributes=["opt"])),
        dict(name="prose", created_by="c", where="w", source="s",
             required=False, observable=False)])


def ext_records(m, sizes, **fields):
    """An extension run whose registry has the declared additions of E2C
    (apart from the `fields` given)."""
    run = rt.ext_run(m, sizes)
    base = dict(structures=["A", "B", "ExtA", "ExtB", "Probe"],
                listeners=["DB", "ext.onload"])
    base.update(fields)
    return rt.edit(run, rt.find(run, "registry"), **base)


def ext_with(**fields):
    return summ(ext_records(M, SIZES, **fields))


DECLARED = {
    "s2": {"total_delta": [
        dict(heap="bin/hol.state", kinds=None, value=0, observed={},
             mechanism="none"),
        dict(heap="bin/hol.state0", kinds=None, value=0, observed={},
             mechanism="none")]},
    "e2c": E2C}


class Chain34(Base34):
    """The stages of the storage gate on fake processes, with the
    declaration patched to the list form of design 8.5."""

    def setUp(self):
        super().setUp()
        patch = mock.patch.object(st.offline, "load_declared",
                                  lambda *a: copy.deepcopy(DECLARED))
        patch.start()
        self.addCleanup(patch.stop)
        patch = mock.patch.object(offline, "check_code", lambda c: None)
        patch.start()
        self.addCleanup(patch.stop)

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
                         offline=self.offline_files(), **extra)
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
                               counts=a.storage_counts,
                               timing_counts=a.timing_counts)[-1]

    @staticmethod
    def finals(folder, report):
        """The final tries [(entry, receipt)] of a stage's archive."""
        receipts = {e["receipt"]: st.check_run(folder, report, e)
                    for e in report["runs"]}
        return st.check_redraws(report, st.check_plan(report), receipts)



class Smoke(Base34):
    def test_a_smoke_run_measures_every_unit_once_per_side(self):
        args, report = self.run_stage("smoke", "smoke")
        self.assertTrue(report["success"], report.get("failure"))
        self.assertTrue(report["outcome"]["facts"]["ok"])
        self.assertEqual(len(report["runs"]), 2 * len(st.UNITS) - 1)


def noop_leak(run, words=1):
    """A release run whose no-op kind retains `words` per object."""
    i = rt.find(run, "live", phase="noop.before")
    j = rt.find(run, "release", release="noop")
    m = run[rt.find(run, "probe")]["params"]["m"]
    run[i:j + 1] = rt.release_rows("release", "release", ("noop",), m,
                                   words)
    return run


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
        again = st.outcome(last["report"], self.finals(folder, last[
            "report"]), folder)
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
        self.assertEqual(first["outcome"]["owed"], [["extend", "ext"],
                                                    ["extend", "graph"]])
        self.assertEqual(st.exit_of(first), 2)
        ext = self.args("second", storage_counts=a.storage_counts,
                        timing_counts=a.timing_counts,
                        first=Path(first["output"]))
        spec = st.extend_spec(ext)
        self.assertEqual(spec["names"], ["graph", "ext"])
        report = st.run(ext, spec)
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(len(report["runs"]), 30)  # ext: candidate only
        self.assertEqual(report["outcome"]["results"]["E2:a"]["mode"],
                         "paired")
        row = report["outcome"]["results"]["S1:fragment"]
        self.assertEqual((row["decision"], row["mode"]), ("pass",
                                                          "paired"))
        chain = st.replay_chain(report["output"], counts=a.storage_counts,
                                timing_counts=a.timing_counts)
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

    def followup_data(self, leak, **patched):
        self.prepared()
        self.world.edits["release", "cand"] = lambda run: noop_leak(
            run, leak)
        a, first = self.decide()
        self.world.edits.clear()
        pre = self.args("pre2", storage_counts=a.storage_counts,
                        timing_counts=a.timing_counts,
                        stage=Path(first["output"]))
        return st.predeclare_followup(pre), first

    def test_the_followup_m_scales_with_the_floor_range(self):
        data, first = self.followup_data(2)
        self.assertEqual(data["floor_range"], 2)
        self.assertEqual(data["base_m"], M)
        # max(4 M, M x range / (1/4)) = 32
        self.assertEqual(data["required_m"], 32)
        self.assertEqual(data["followup"]["m"], 32)
        self.assertFalse(data["capped"])
        self.assertEqual(data["m_cap"], st.cap_of(
            data["object_cpu"], data["m0"], st.FOLLOWUP_FACTOR))

    def test_a_small_floor_range_still_quadruples_m(self):
        data, first = self.followup_data(1)
        self.assertEqual(data["required_m"], M * st.FOLLOWUP_FACTOR)

    def test_the_followup_cap_is_four_times_the_budget(self):
        with mock.patch.object(st, "RELEASE_BUDGET_S", 0.1):
            data, first = self.followup_data(2)
            self.assertTrue(data["capped"])
            self.assertEqual(data["followup"]["m"], data["m_cap"])
            self.assertEqual(data["m_cap"], st.cap_of(
                data["object_cpu"], data["m0"], 4))
            st.check_sizing(data)
            data["followup"]["m"] += 1
            with self.assertRaisesRegex(dw.Refusal, "disagree"):
                st.check_sizing(data)

    def test_an_unresolved_floor_is_followed_up_at_a_larger_m(self):
        self.prepared()
        self.world.edits["release", "cand"] = noop_leak
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
                                followup_counts=out,
                                timing_counts=a.timing_counts)
        self.assertEqual([e["stage"] for e in chain], ["run", "followup"])
        self.assertEqual(st.final_rows(chain)["R1:simpset"]["stage"],
                         "followup")
        self.assertEqual(st.owed_units(chain, "followup"), [])


def incomparable(run):
    """A release run whose readings of one kind differ in gc_share."""
    i = rt.find(run, "live", phase="simpset.after")
    return rt.edit(run, i, gc_share=1)


def held_incomparable(run):
    """A release run whose `held` reading alone is not comparable."""
    i = rt.find(run, "live", phase="simpset.held")
    return rt.edit(run, i, gc_share=1)


def anchor_moved(run):
    """A graph run in which the anchor of one kind and size moved."""
    i = rt.find(run, "graph", graph="fragment", n=100)
    return rt.edit(run, i, anchor_post=run[i]["anchor"] + 3)


class Redraws(Chain34):
    def tries(self, report, unit, side):
        return [e for e in report["runs"] if e["workload"] == unit
                and e["side"] == side]

    def test_a_not_comparable_process_is_redrawn(self):
        self.once("release", "cand", incomparable)
        args, report = self.run_stage("smoke", "smoke")
        self.assertTrue(report["success"], report.get("failure"))
        runs = self.tries(report, "release", "cand")
        self.assertEqual([(e["redraw"], e["accepted"]) for e in runs],
                         [(0, False), (1, True)])
        self.assertTrue(runs[0]["superseded"])
        self.assertIsNone(runs[1]["superseded"])
        self.assertTrue(runs[1]["receipt"].endswith("-r1.json.gz"))
        folder = Path(report["output"])
        info = st.replay_chain(folder)[-1]["info"]
        self.assertEqual(info["replayed"], len(report["runs"]))

    def test_a_process_that_never_compares_is_a_refusal(self):
        self.world.edits["release", "cand"] = incomparable
        args, report = self.run_stage("smoke", "smoke")
        self.assertFalse(report["success"])
        self.assertIn("process rejected", report["failure"])
        self.assertEqual(len(self.tries(report, "release", "cand")),
                         st.MAX_REDRAWS + 1)

    def test_a_not_comparable_held_reading_alone_is_accepted(self):
        run = held_incomparable(rt.release_run(M))
        s = summ(run)
        self.assertFalse(s["held_comparable"]["simpset"])
        self.assertTrue(s["held_comparable"]["noop"])
        self.once("release", "cand", held_incomparable)
        args, report = self.run_stage("smoke", "smoke")
        self.assertTrue(report["success"], report.get("failure"))
        # one process in the group has no comparable held reading of the
        # kind: the group is redrawn (below), not the reading refused
        self.assertEqual([e["redraw"] for e in self.tries(
            report, "release", "cand")], [0, 1])

    def test_a_group_without_a_comparable_held_reading_is_redrawn(self):
        self.once("release", "cand", held_incomparable)
        args, report = self.run_stage("smoke", "smoke")
        self.assertTrue(report["success"], report.get("failure"))
        first, again = self.tries(report, "release", "cand")
        self.assertIn("no comparable held reading of simpset",
                      first["superseded"])
        self.assertTrue(first["accepted"] and again["accepted"])
        self.assertEqual(self.tries(report, "release", "base")[0][
            "superseded"], None)
        self.replayed(report, argparse.Namespace(storage_counts=None)) \
            if False else st.replay_chain(report["output"])

    def test_a_held_gap_that_persists_is_a_refusal(self):
        self.world.edits["release", "cand"] = held_incomparable
        args, report = self.run_stage("smoke", "smoke")
        self.assertFalse(report["success"])
        self.assertIn("no comparable held reading", report["failure"])
        self.assertEqual(len(self.tries(report, "release", "cand")),
                         st.MAX_REDRAWS + 1)

    def test_a_comparable_process_of_the_group_covers_the_gap(self):
        self.prepared()
        self.once("release", "cand", held_incomparable)
        a, report = self.decide()
        self.assertTrue(report["success"], report.get("failure"))
        runs = self.tries(report, "release", "cand")
        self.assertEqual(len(runs), 3)
        self.assertTrue(all(e["superseded"] is None for e in runs))
        self.assertEqual(self.replayed(report, a)["info"]["exit"], "pass")

    def test_an_anchor_moved_in_one_process_is_redrawn(self):
        self.once("graph", "cand", anchor_moved)
        args, report = self.run_stage("smoke", "smoke")
        self.assertTrue(report["success"], report.get("failure"))
        first, again = self.tries(report, "graph", "cand")
        self.assertIn("anchor moved", first["superseded"])
        self.assertTrue(first["accepted"])
        self.assertIsNone(again["superseded"])
        st.replay_chain(report["output"])

    def test_an_anchor_that_keeps_moving_fails_s1_on_the_candidate(self):
        self.prepared()
        self.world.edits["graph", "cand"] = anchor_moved
        a, report = self.decide()
        self.assertTrue(report["success"], report.get("failure"))
        self.assertEqual(len(self.tries(report, "graph", "cand")),
                         3 * (st.MAX_REDRAWS + 1))
        rows = report["outcome"]["results"]
        self.assertEqual(rows["S1:fragment"]["decision"], "fail")
        self.assertEqual(self.replayed(report, a)["info"]["exit"], "fail")

    def test_an_anchor_that_keeps_moving_on_the_baseline_refuses(self):
        self.world.edits["graph", "base"] = anchor_moved
        args, report = self.run_stage("smoke", "smoke")
        self.assertFalse(report["success"])
        self.assertIn("anchor moved", report["failure"])

    def test_a_redraw_does_not_hide_another_rejection(self):
        """A not comparable output that also fails an admission check
        (here: a stray write) is refused, not redrawn."""
        self.world.edits["release", "cand"] = incomparable
        self.world.fault = lambda name, side, n: (
            "stray" if name == "release" and side == "cand" else None)
        args, report = self.run_stage("smoke", "smoke")
        self.assertFalse(report["success"])
        self.assertEqual(len(self.tries(report, "release", "cand")), 1)
        self.assertIn("stray", report["failure"])

    def test_the_replay_refuses_a_redraw_that_is_not_one(self):
        self.once("release", "cand", incomparable)
        args, report = self.run_stage("smoke", "smoke")
        path = Path(report["output"]) / "downstream.json"
        data = json.loads(path.read_text())
        for e in data["runs"]:
            if e["redraw"] == 1:
                e["redraw"] = 2  # not consecutive
        path.write_text(dw.dumps(data))
        with self.assertRaises(dw.Refusal):
            st.replay_chain(report["output"])
        data = json.loads(path.read_text())
        for e in data["runs"]:
            if e["redraw"] == 2:
                e["redraw"] = 1
            if e.get("superseded"):
                e["superseded"] = "invented"
        path.write_text(dw.dumps(data))
        with self.assertRaises(dw.Refusal):
            st.replay_chain(report["output"])

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
                         control=self.world.tmp / "control",
                         offline=self.offline_files())
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
                         control=self.world.tmp / "control",
                         offline=self.offline_files())
        with self.assertRaisesRegex(dw.Refusal, "decision configuration"):
            st.predeclare_run(args)

    def test_an_over_cap_pilot_is_clamped_not_refused(self):
        self.stage("smoke", "smoke")
        self.world.edits["release", "base"] = self.world_noise
        with mock.patch.object(st, "RELEASE_BUDGET_S", 10):
            pilot = self.pilot()
            out = pilot["outcome"]
            self.assertTrue(out["capped"])
            self.assertGreater(out["required_m"], out["m_cap"])
            self.assertEqual(out["m"], out["m_cap"])
            self.assertEqual(out["budget_s"], 10)
            self.assertEqual(st.exit_of(pilot), 0)
            # the controls take the clamped M
            spec = st.info_spec(self.args(
                "c", pilot=self.world.tmp / "pilot"), "control")
        self.assertEqual(spec["params"]["m"], out["m_cap"])

    def test_the_cap_is_the_budget_over_the_cpu_per_object(self):
        with mock.patch.object(st, "RELEASE_BUDGET_S", 600):
            self.assertEqual(st.cap_of(0.5, 4), 1200)
            self.assertEqual(st.cap_of(0.5, 4, 4), 4800)
            self.assertEqual(st.cap_of(1000, 7), 7)  # never under M0
        procs = [dict(usage=dict(utime=2.0, stime=0.0))] * 3
        self.assertEqual(st.object_cpu(procs, 10), 2.0 / (
            10 * len(records.RELEASE_KINDS)))

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
        self.assertNotIn("covered", out)
        self.assertEqual(out["m_cap"], st.cap_of(out["object_cpu"], M))
        self.assertEqual(out["budget_s"], st.RELEASE_BUDGET_S)
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
                               counts=a.storage_counts,
                               timing_counts=a.timing_counts)[-1]
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


    def test_a_refused_audit_is_a_judged_attempt_not_a_void_one(self):
        """The execution of run.py is the stage's measuring entry: an audit
        that leaves no receipt fails the stage but still counts as the
        draw (a void attempt could be redrawn without end)."""
        self.install(cases=0)
        script = self.world.roots["cand"] / "src/simp/tests/api-audit/run.py"
        script.write_text("import sys\nsys.exit(0)\n")
        a, report = self.audit()
        self.assertFalse(report["success"])
        self.assertIn("receipts", report["failure"])
        (entry,) = report["runs"]
        self.assertEqual((entry["workload"], entry["accepted"]),
                         (st.AUDIT_UNIT, True))
        state, found = dw.read_ledger(self.world.ledger(), st.LEDGER_TABLE)
        (key,) = [k for k in found if k[1] == "audit"]
        self.assertIn("measuring process was admitted",
                      dw.judged_because(key[0], key[1], found[key]))

    def test_the_audit_entry_is_replayed_against_the_report(self):
        self.install()
        a, report = self.audit()
        path = Path(report["output"]) / "downstream.json"
        data = json.loads(path.read_text())
        data["audit"]["exit"] = 3
        path.write_text(dw.dumps(data))
        with self.assertRaises(dw.Refusal):
            st.replay_chain(report["output"], counts=a.storage_counts,
                            timing_counts=a.timing_counts)


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
        self.disposition()

    def harvest(self, **change):
        path = self.evidence / "harvest.json"
        path.write_text(dw.dumps(dict(dict(
            schema=offline.SCHEMA, command="harvest", success=True),
            **change)))
        Path(str(path) + ".seal").write_text(dw.dumps(acc.seal(path)))

    def disposition(self, **change):
        """A sealed disposition.json that owes nothing."""
        path = self.evidence / "disposition.json"
        path.write_text(dw.dumps(dict(dict(
            schema=dispose.SCHEMA, status="pass", owed=[],
            attribution_needed=[]), **change)))
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
        patch = mock.patch.object(st, "SCRATCH_ROOT", self.tree.scratch_root)
        patch.start()
        self.addCleanup(patch.stop)

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

    def test_a_scratch_root_other_than_the_declared_one_is_refused(self):
        t = self.tree
        for name in ("precious", "t33"):
            other = t.tmp / name / "t33"
            other.mkdir(parents=True)
            self.refused("declared", scratch_root=other)
            self.assertTrue(other.exists())

    def test_the_declared_scratch_root_is_the_one_the_drivers_use(self):
        self.assertEqual(Path(st.__dict__["SCRATCH_ROOT"]).name, "t33")
        self.assertEqual(st.SCRATCH_ROOT, self.tree.scratch_root)
        self.assertEqual(
            dispose.storage.SCRATCH_ROOT, self.tree.scratch_root)

    def test_a_disposition_is_required_and_must_be_sealed(self):
        t = self.tree
        path = t.evidence / "disposition.json"
        Path(str(path) + ".seal").write_text(
            dw.dumps(dict(sha256="0" * 64, bytes=1)))
        self.refused("disposition seal")
        path.unlink()
        self.refused("0 disposition.json")

    def test_a_disposition_that_still_owes_something_is_refused(self):
        t = self.tree
        t.disposition(owed=[dict(kind="simpset")])
        self.refused("still owes")
        t.disposition(attribution_needed=[dict(unit="load-simpLib")])
        self.refused("still owes")

    def test_a_disposition_of_another_schema_is_refused(self):
        self.tree.disposition(schema="other")
        self.refused("not a")

    def test_an_intent_journal_is_written_before_anything_is_removed(self):
        t = self.tree
        seen = []
        real = dispose.remove_path

        def look(path, how):
            seen.append((t.evidence / "snapshot-disposal.intent.json"
                         ).is_file())
            return real(path, how)
        with mock.patch.object(dispose, "remove_path", look), \
                contextlib.redirect_stdout(io.StringIO()):
            dispose.dispose_snapshots(t.args())
        self.assertTrue(seen and all(seen))
        self.assertFalse(
            (t.evidence / "snapshot-disposal.intent.json").exists())

    def test_an_interrupted_disposal_is_resumed_from_its_journal(self):
        t = self.tree
        real = dispose.remove_path
        count = []

        def die(path, how):
            count.append(path)
            if len(count) == 3:
                raise KeyboardInterrupt
            return real(path, how)
        with mock.patch.object(dispose, "remove_path", die):
            with self.assertRaises(KeyboardInterrupt):
                dispose.dispose_snapshots(t.args())
        self.assertTrue(
            (t.evidence / "snapshot-disposal.intent.json").is_file())
        gone = [p for p in t.listed() if not p.exists()]
        self.assertTrue(gone and len(gone) < len(t.listed()))
        # the snapshots are no longer whole, and the verification which
        # would fail on them is not repeated
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(dispose.dispose_snapshots(t.args(
                verify_argv=[sys.executable, "-c",
                             "raise SystemExit(1)"])), 0)
        for path in t.listed():
            self.assertFalse(path.exists(), path)
        data = json.loads((t.evidence / "snapshot-disposal.json"
                           ).read_text())
        self.assertTrue(data["resumed"])
        self.assertIsNone(data["verify"])
        self.assertFalse(
            (t.evidence / "snapshot-disposal.intent.json").exists())

    def test_a_journal_of_another_plan_is_not_resumed(self):
        t = self.tree
        journal = t.evidence / "snapshot-disposal.intent.json"
        journal.write_text(dw.dumps(dict(
            schema=dispose.INTENT_SCHEMA, paths=[["/x", "tree"]])))
        self.refused("another plan")


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

    @staticmethod
    def fake_chain(results, reported=None):
        return [dict(stage="run", report=dict(
            attempt="a", outcome=dict(results=results,
                                      reported=reported or {})))]

    def test_a_kind_missing_from_a_run_is_blocked(self):
        full = {}
        for case, kind in dispose.expected_storage():
            if case in ("L1", "L3", "S2") or (case, kind) == ("S1",
                                                              "merge"):
                full[rules.key_of(case, kind)] = dict(
                    rules.row(case, kind, "pass", "ok"), stage="x")
        results = {k: rules.row(r["case"], r["kind"], "pass", "ok")
                   for k, r in full.items()}
        got, _ = dispose.storage_decisions([self.fake_chain(results)])
        by = {(x["case"], x["kind"]): x for x in got}
        self.assertEqual(by[("S1", "merge")]["decision"], "pass")
        for key in (("S1", "fragment"), ("R1", "simpset"), ("E2", "a")):
            self.assertEqual(by[key]["decision"], "blocked", key)
            self.assertIn("no evidence", by[key]["reason"])
        gone = dict(results)
        del gone["L1:state-empty"]
        got, _ = dispose.storage_decisions([self.fake_chain(gone)])
        by = {(x["case"], x["kind"]): x for x in got}
        self.assertEqual(by[("L1", "state-empty")]["decision"], "blocked")

    def test_reported_and_unsupported_rows_are_decisions(self):
        reported = {
            "S4:allocation": rules.s4_row(),
            "E2:u": rules.row("E2", "u", "reported", "u grew"),
            "times": {"graph": {}}}
        got, _ = dispose.storage_decisions([self.fake_chain(
            {}, reported)])
        by = {(x["case"], x["kind"]): x["decision"] for x in got}
        self.assertEqual(by[("S4", "allocation")], "unsupported")
        self.assertEqual(by[("E2", "u")], "reported")
        self.assertNotIn(("times", "graph"), by)

    def test_rows_owed_or_inconclusive_close_as_blocked(self):
        for decision, owed in (("pass", "extend"), ("inconclusive", None),
                               ("inconclusive", "followup")):
            r = rules.row("S1", "fragment", decision, "why", owed)
            self.assertEqual(dispose.closed(r), "blocked")
        for decision in ("pass", "fail"):
            self.assertEqual(dispose.closed(rules.row(
                "S1", "fragment", decision, "why")), decision)

    def test_the_units_an_owed_row_needs(self):
        row = lambda case, kind: rules.row(case, kind, "inconclusive", "w")
        self.assertEqual(st.row_units(row("S1", "merge")), (st.GRAPH,))
        self.assertEqual(st.row_units(row("E2", "a")), (st.EXT, st.GRAPH))
        self.assertEqual(st.row_units(row("E2", "b")), (st.EXT,))
        self.assertEqual(st.row_units(row("L1", "first-use")),
                         ("registry-first-use",))

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

    intervals = dict(wall=[0.9, 1.0], cpu=[0.9, 1.0], gc_cpu=[0.9, 1.0],
                     maxrss=[0.9, 1.0])

    def dispose(self, stages, a, first, out="disposition.json", **extra):
        w = self.world
        timing = [dict(report=dict(
            repo=str(w.repo), base=first["base"], cand=first["cand"],
            key=first["key"], manifest=first["manifest"]), stage="first")]
        disp = dict(workloads={"load-simpLib": dict(
            status="pass", note="", stages=[dict(
                stage="first", intervals=self.intervals)])})
        args = argparse.Namespace(**dict(dict(
            stage=[Path(r["output"]) for r in stages],
            timing_stage=w.tmp / "timing", offline=self.offline_files(),
            repo=w.repo, ledger=None, timing_counts=a.timing_counts,
            storage_counts=a.storage_counts, timing_followup_counts=None,
            storage_followup_counts=None, relocated=[],
            out=w.tmp / out), **extra))
        with mock.patch.object(dw, "replay_chain", lambda *x: timing), \
                mock.patch.object(dw, "disposition",
                                  lambda *x: disp), \
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
        got = {(x["case"], x["kind"]): x["decision"]
               for x in data["decisions"]}
        self.assertEqual(got[("S4", "allocation")], "unsupported")
        self.assertEqual(got[("E2", "u")], "reported")
        self.assertEqual(sorted(data["offline"]),
                         ["archive", "audit", "harvest"])
        self.assertEqual(len(data["storage_chains"]), 2)
        self.assertEqual(data["ledgers"]["storage"]["attempts"][-1][
            "statuses"], ["pass"])
        self.assertEqual(data["code"], dw.code_seals())

    def test_a_missing_audit_stage_blocks_its_cases(self):
        self.prepared()
        a, first = self.decide()
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

    def test_the_disposition_is_sealed(self):
        a, first, audit = self.stages()
        code, out = self.dispose([first, audit], a, first)
        self.assertEqual(json.loads(Path(str(out) + ".seal").read_text()),
                         acc.seal(out))
        data = json.loads(out.read_text())
        self.assertEqual(data["schema"], dispose.SCHEMA)
        self.assertEqual(data["owed"], [])

    def test_an_owed_row_after_the_last_stage_is_blocked(self):
        self.prepared()
        self.once("graph", "cand", lambda run: grow(run, "fragment", 100))
        a, first = self.decide()
        code, out = self.dispose([first], a, first)
        data = json.loads(out.read_text())
        self.assertEqual(code, 2)
        got = {(x["case"], x["kind"]): x for x in data["decisions"]}
        row = got[("S1", "fragment")]
        self.assertEqual(row["decision"], "blocked")
        self.assertEqual(row["owed"], "extend")
        self.assertIn("after the last stage", row["reason"])
        self.assertIn(("S1", "fragment"), [(x["case"], x["kind"])
                                           for x in data["owed"]])

    def test_an_inconclusive_row_after_the_last_stage_is_blocked(self):
        self.prepared()
        self.world.edits["release", "cand"] = noop_leak
        a, first = self.decide()
        self.assertEqual(first["outcome"]["results"]["R1:simpset"][
            "decision"], "inconclusive")
        code, out = self.dispose([first], a, first)
        got = {(x["case"], x["kind"]): x["decision"] for x in
               json.loads(out.read_text())["decisions"]}
        self.assertEqual(got[("R1", "simpset")], "blocked")

    def test_a_second_deciding_attempt_is_a_branch(self):
        """The driver refuses a second judged draw itself; the disposition
        does not rely on that: a deciding attempt of the gate in the ledger
        and in no chain is a branch."""
        self.prepared()
        a, first = self.decide()
        chain = st.replay_chain(first["output"], counts=a.storage_counts,
                                timing_counts=a.timing_counts)
        real = dw.read_ledger

        def with_branch(path, table=None):
            state, found = real(path, table)
            (mine,) = found.values()
            found[("run-branch", "extend")] = dict(
                opens=mine["opens"], closes=[dict(status="pass")])
            return state, found
        dispose.check_linear([chain], self.world.ledger())
        with mock.patch.object(dw, "read_ledger", with_branch):
            with self.assertRaisesRegex(dw.Refusal, "branch.*run-branch"):
                dispose.check_linear([chain], self.world.ledger())

    def test_the_chains_are_the_runs_and_the_audits_once_each(self):
        self.prepared()
        a, first = self.decide()
        with self.assertRaisesRegex(dw.Refusal, "once each"):
            self.dispose([first, first], a, first)

    def test_process_redraws_are_listed(self):
        self.prepared()
        self.once("release", "cand", incomparable)
        a, first = self.decide()
        code, out = self.dispose([first], a, first)
        data = json.loads(out.read_text())
        (one,) = data["process_redraws"]
        self.assertEqual((one["unit"], one["side"], one["redraw"]),
                         ("release", "cand", 0))
        self.assertEqual(one["stage"], "run")
        self.assertTrue(one["reason"])

    def test_gc_and_rss_intervals_wholly_above_the_margin_owe_attribution(
            self):
        self.prepared()
        a, first = self.decide()
        self.intervals = dict(self.intervals, gc_cpu=[1.1, 1.3],
                              maxrss=[1.01, 1.2])
        code, out = self.dispose([first], a, first)
        data = json.loads(out.read_text())
        mine = [x for x in data["attribution_needed"]
                if x.get("source") == "timing"]
        self.assertEqual([(x["unit"], x["field"]) for x in mine],
                         [("load-simpLib", "gc_cpu")])

    def test_the_offline_reports_must_be_the_ones_the_counts_bound(self):
        a, first, audit = self.stages()
        other = self.world.tmp / "other"
        other.mkdir()
        files = []
        for command in ("archive", "audit", "harvest"):
            path = other / ("%s.json" % command)
            path.write_text(dw.dumps(offline_report(
                command, [check_of("different", "S3")], above=[])))
            Path(str(path) + ".seal").write_text(dw.dumps(acc.seal(path)))
            files.append(path)
        with mock.patch.object(Disposition, "offline_files",
                               lambda self: files):
            with self.assertRaisesRegex(dw.Refusal, "storage counts"):
                self.dispose([first, audit], a, first)

    def test_relocated_entries_go_to_the_table_of_their_information_run(
            self):
        self.info_stages()
        w = self.world
        state, found = dw.read_ledger(w.ledger(), st.LEDGER_TABLE)
        names = sorted(r["attempt"] for r in dw.table_lines(
            state, st.LEDGER_TABLE) if r["event"] == "info")
        shares = dispose.split_relocated(w.ledger(), {
            names[0]: "/x", names[1]: "/y"})
        self.assertEqual(shares[st.LEDGER_TABLE], {names[0]: "/x",
                                                   names[1]: "/y"})
        self.assertEqual(shares[dw.TABLE], {})
        with self.assertRaisesRegex(dw.Refusal, "names no information"):
            dispose.split_relocated(w.ledger(), {"nothing": "/z"})

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
                         control=self.world.tmp / "control",
                         offline=self.offline_files())
        data = st.predeclare_run(args)
        out = self.world.repo / "src/simp/tests/performance/counts.json"
        out.write_text(dw.dumps(data))  # written, not committed
        run = self.args("first", timing_counts=counts, storage_counts=out)
        with self.assertRaisesRegex(dw.Refusal, "not committed"):
            st.run_spec(run)

    def test_predeclare_needs_the_three_offline_reports(self):
        self.info_stages()
        counts = self.timing_counts()
        files = self.offline_files()
        for given in (files[:2], files + files[:1]):
            args = self.args("pre", timing_counts=counts,
                             smoke=self.world.tmp / "smoke",
                             pilot=self.world.tmp / "pilot",
                             control=self.world.tmp / "control",
                             offline=given)
            with self.assertRaisesRegex(dw.Refusal, "S3 reports|two"):
                st.predeclare_run(args)

    def test_the_timing_counts_seal_is_checked_at_run_and_replay(self):
        self.info_stages()
        self.predeclare_done = self.predeclare()
        a, data, out = self.predeclare_done
        timing = data_timing(self)
        self.assertEqual(data["timing_counts"]["seal"], acc.seal(timing))
        run = self.args("first", timing_counts=timing, storage_counts=out)
        st.run_spec(run)  # as predeclared
        other = self.world.tmp / "other-counts.json"
        other.write_text(timing.read_text() + " ")
        run = self.args("first", timing_counts=other, storage_counts=out)
        with self.assertRaisesRegex(dw.Refusal, "other timing counts"):
            st.run_spec(run)
        _, report = self.decide()
        with self.assertRaisesRegex(dw.Refusal, "other timing counts"):
            st.replay_chain(report["output"], counts=out,
                            timing_counts=other)

    def test_the_saved_state_bytes_come_from_the_manifest(self):
        a, report = self.go()
        manifest = json.loads(self.world.manifest.read_text())
        heaps = {u["heap"] for u in report["units"].values()}
        want = {side: {h: manifest["sides"][side]["products"][h]["bytes"]
                       for h in heaps} for side in ("base", "cand")}
        self.assertEqual(report["heap_bytes"], want)
        self.assertEqual(report["outcome"]["reported"]["heap_bytes"], want)

    def test_a_heap_the_manifest_does_not_list_refuses(self):
        report = dict(units={"u": dict(heap="bin/hol.state9")})
        manifest = dict(sides={s: dict(products={}) for s in
                               ("base", "cand")})
        with self.assertRaisesRegex(dw.Refusal, "lists no"):
            st.heap_bytes(report, manifest)

    def test_predeclare_refuses_uncommitted_timing_counts(self):
        self.info_stages()
        counts = self.timing_counts()
        counts.write_text(counts.read_text() + " ")
        args = self.args("pre", timing_counts=counts,
                         smoke=self.world.tmp / "smoke",
                         pilot=self.world.tmp / "pilot",
                         control=self.world.tmp / "control",
                         offline=self.offline_files())
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
        self.assertEqual((data["required_m"], data["capped"]), (M, False))
        self.assertEqual(data["m_cap"], st.cap_of(data["object_cpu"], M))
        self.assertEqual(data["budget_s"], st.RELEASE_BUDGET_S)
        self.assertEqual(data["timing_counts"]["seal"], acc.seal(
            self.world.repo / "src/simp/tests/performance/"
            "task33_counts.json"))
        data["capped"] = True
        out.write_text(dw.dumps(data))
        with self.assertRaisesRegex(dw.Refusal, "disagree"):
            sides, mseal = dw.pins_of(self.args("x"))
            st.load_storage_counts(out, sides, "run", self.world.repo,
                                   mseal, data_timing(self),
                                   committed=False)


def data_timing(test):
    return test.world.repo / "src/simp/tests/performance/" \
        "task33_counts.json"


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
