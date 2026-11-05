#!/usr/bin/env python3
"""TASK29B allocation matrix: protocol, decision rule and replay controls.

Synthetic in-test fixtures only; no runtime, toolchain or committed receipt.
Every guard in a table below must be killed by a mutation of that guard.
"""
from fractions import Fraction
import json
from pathlib import Path
import re
import shutil
import tempfile
import unittest

import acceptance as a
import allocation_analysis as an
import allocation_matrix as m
import allocation_schema as sc
import allocation_testbed as tb
import task29_gate as gate
from allocation_testbed import (CASE, LIB, ALIAS, STEADY, experiment,
                                observation, process_events)


def pattern(*words):
    return ".*".join(words)


# ---------------------------------------------------------------- protocol

def with_events(change, **kw):
    def build():
        events = process_events(**kw)
        change(events)
        return events, {}
    return build


def with_rows(change, **kw):
    return lambda: (process_events(mutate=change, **kw), {})


def other_binding(**kw):
    return lambda: (process_events(), kw)


def named(events, name):
    return [i for i, e in enumerate(events) if e[1:2] == ["alloc." + name]][0]


def set_event(name, text, nth=0):
    def change(events):
        events[named(events, name) + nth][2] = text
    return change


def endpoint_text(**kw):
    point = tb.point(kw.get("counts", {}), kw.get("overflow", 0),
                     kw.get("word", 8), kw.get("abi", 1))
    return tb.text(point)


def bracket_text(index, start, end):
    return "%s;%s;%s" % (index, start, end)


def last_end(value):
    """The last bracket ends at exactly `value` words (total consistent)."""
    def change(rows):
        end = rows[-1][3]
        other = sum(end[5:])
        end[3], end[4] = value, value - other
    return change


def at_rows(i, j, k, value):
    """rows[i][j][k] = value (j: 2 start, 3 end)."""
    def change(rows):
        rows[i][j][k] = value
    return change


def four_repeats_config_says_three():
    events = process_events(repeats=4)
    events[0][2] = events[0][2].replace(",4,15,", ",3,15,")
    return events, dict(repeats=4)


STEADY_ROW = 6   # first operation_steady bracket (startup is row 0)
GUARDS = [
    ("exception", with_events(lambda e: e.append(["exception", "Fail", "x"])),
     "exception"),
    ("extra observation", with_events(lambda e: e.insert(2, e[2])),
     "observation count"),
    ("missing bracket", with_events(lambda e: e.pop(2)),
     "observation count"),
    ("bracket order", with_events(
        lambda e: e.__setitem__(slice(4, 6), [e[5], e[4]])),
     "bracket order"),
    ("duplicate name for apply", with_events(
        lambda e: e.__setitem__(-3, list(e[4]))), "bracket order"),
    ("foreign-thread counter missing", with_events(
        lambda e: e.pop(-2)), "observation count"),
    ("foreign-thread counter nonzero", with_events(
        lambda e: e[-2].__setitem__(2, "1,0")), "foreign-thread"),
    ("reserved path word nonzero", with_events(
        lambda e: e[-2].__setitem__(2, "0,1")), "foreign-thread"),
    ("foreign-thread record misnamed", with_events(
        lambda e: e[-2].__setitem__(1, "alloc.other")), "foreign-thread"),
    ("foreign-thread record misplaced", with_events(
        lambda e: e.insert(2, e.pop(-2))), "bracket order|foreign-thread"),
    ("bracket event with an extra field", with_events(
        lambda e: e[3].append("x")), "bracket order"),
    ("wrong event kind", with_events(
        lambda e: e[2].__setitem__(0, "check")), "bracket order"),
    ("config missing", with_events(
        lambda e: e[0].__setitem__(1, "alloc.other")), "configuration"),
    ("config extra field", with_events(lambda e: e[0].append("x")),
     "configuration"),
    ("config case", other_binding(case="frag_named"), "binding"),
    ("config size", other_binding(size=10), "binding"),
    ("config steady", other_binding(steady=8), "binding"),
    ("config abi", with_events(
        lambda e: e[0].__setitem__(2, e[0][2].replace(",15,", ",14,"))),
     "binding"),
    ("config repeats", four_repeats_config_says_three, "binding"),
    ("config canary array", with_events(
        lambda e: e[0].__setitem__(2, e[0][2].rsplit(",", 1)[0] + ",999")),
     "binding"),
    ("completion check name", with_events(
        lambda e: e.__setitem__(-1, ["check", "other", "pass"])),
     "completion"),
    ("completion check result", with_events(
        lambda e: e.__setitem__(-1, ["check", "allocation brackets",
                                     "fail"])), "completion"),
    ("completion missing", with_events(lambda e: e.pop()),
     "observation count"),
    ("steady index repeated", with_events(set_event(
        "operation_steady", bracket_text(0, endpoint_text(), endpoint_text()),
        2)), "bracket index"),
    ("steady index skipped", with_events(
        lambda e: e[named(e, "operation_steady") + 1].__setitem__(
            2, "2" + e[named(e, "operation_steady") + 1][2][1:])),
     "bracket index"),
    ("nonsteady index", with_events(
        lambda e: e[named(e, "setup")].__setitem__(
            2, "1" + e[named(e, "setup")][2][1:])), "bracket index"),
    ("malformed record", with_events(set_event("setup", "0;1,2")),
     "malformed bracket"),
    ("record with four parts", with_events(set_event("setup", "0;1;2;3")),
     "malformed bracket"),
    ("endpoint too short", with_events(set_event(
        "setup", bracket_text(0, "1,8,0,3,3", endpoint_text()))),
     "malformed endpoint"),
    ("endpoint leading zero", with_events(set_event(
        "setup", bracket_text(0, endpoint_text().replace("1,8", "01,8"),
                              endpoint_text()))), "malformed endpoint"),
    ("endpoint negative", with_events(set_event(
        "setup", bracket_text(0, "-1,8,0,0,0,0,0,0", endpoint_text()))),
     "malformed endpoint"),
    ("endpoint too long", with_events(set_event(
        "setup", bracket_text(0, "1,8,0,3,3,0,0,0,0", endpoint_text()))),
     "malformed endpoint"),
    ("endpoint not a number", with_events(set_event(
        "setup", bracket_text(0, "x,8,0,0,0,0,0,0", endpoint_text()))),
     "malformed endpoint"),
    ("endpoint empty field", with_events(set_event(
        "setup", bracket_text(0, "1,8,0,,0,0,0,0", endpoint_text()))),
     "malformed endpoint"),
    ("endpoint beyond uint64", with_rows(last_end(2 ** 64)), "uint64"),
    ("wrong ABI", with_rows(at_rows(3, 2, 0, 2)), "ABI"),
    ("compact32 word size", with_rows(at_rows(0, 2, 1, 4)), "word size"),
    ("overflow mask", with_rows(at_rows(3, 3, 2, 4)), "overflow"),
    ("total differs from categories", with_rows(at_rows(2, 3, 3, 1)),
     "category sum"),
    ("decreasing inside a bracket", with_rows(
        lambda r: (r[4].__setitem__(2, r[4][3]), r[4].__setitem__(
            3, tb.point(dict.fromkeys(tb.CATEGORIES, 1))))),
     "non-monotonic bracket"),
    ("decreasing across brackets", with_rows(
        lambda r: (r[5].__setitem__(2, tb.point({})),
                   r[5].__setitem__(3, tb.point({"native": 1})))),
     "non-monotonic across"),
    ("startup reports nothing", with_rows(lambda r: None, start=0),
     "no startup"),
    ("fewer than three repeats", lambda: (process_events(repeats=2),
                                          dict(repeats=2)), "three"),
]


class Protocol(unittest.TestCase):
    def test_valid_process(self):
        brackets, _ = tb.parsed(work={"setup": {"native": 5, "rts": 2}})
        by = {b["name"]: sc.deltas(b) for b in brackets}
        self.assertEqual(by["setup"]["total"], 7)
        self.assertEqual(by["setup"]["heap"], 7)
        self.assertEqual(by["empty"]["total"], 4)
        self.assertEqual(by["canary"]["total"] - by["empty"]["total"],
                         sum(sc.CANARY.values()))
        self.assertEqual(by["startup"]["total"], 4000)
        self.assertEqual([b["name"] for b in brackets], sc.names(3))

    def test_other_steady_repeat_counts_parse(self):
        for repeats in (3, 4, 7):
            with self.subTest(repeats=repeats):
                brackets, _ = tb.parsed(repeats=repeats)
                self.assertEqual(
                    [b["index"] for b in brackets
                     if b["name"] == "operation_steady"],
                    list(range(repeats)))
        with self.assertRaisesRegex(sc.InvalidAllocation, "observation"):
            sc.parse(process_events(repeats=5), case=CASE, size=0,
                     steady=STEADY, repeats=4)

    def test_code_stays_visible_and_heap_excludes_it(self):
        brackets, _ = tb.parsed(work={"apply": {"native": 2, "code": 9}})
        d = sc.deltas(brackets[-1])
        self.assertEqual((d["code"], d["total"], d["heap"]), (9, 11, 2))

    def test_guard_table(self):
        for label, build, message in GUARDS:
            with self.subTest(label):
                events, override = build()
                kw = dict(case=CASE, size=0, steady=STEADY, repeats=3)
                kw.update(override)
                with self.assertRaisesRegex(sc.InvalidAllocation, message):
                    sc.parse(events, **kw)

    def test_uint64_boundary(self):
        brackets, _ = sc.parse(
            process_events(mutate=last_end(2 ** 64 - 1)), case=CASE, size=0,
            steady=STEADY, repeats=3)
        self.assertEqual(brackets[-1]["end"]["total"], 2 ** 64 - 1)
        with self.assertRaisesRegex(sc.InvalidAllocation, "uint64"):
            sc.parse(process_events(mutate=last_end(2 ** 64)), case=CASE,
                     size=0, steady=STEADY, repeats=3)

    def test_canary_must_cost_exactly_its_known_words(self):
        for category in tb.CATEGORIES:
            for change in (1, -1):
                with self.subTest(category=category, change=change):
                    cost = dict(tb.default_cost("canary"))
                    if cost.get(category, 0) + change < 0:
                        continue
                    cost[category] = cost.get(category, 0) + change
                    # The category check itself must fire: a cost above the
                    # known words would otherwise be caught only by the
                    # total, under a different message.
                    with self.assertRaisesRegex(
                            sc.InvalidAllocation,
                            "canary %s words" % category):
                        tb.parsed(work={"canary": cost})

    def test_a_word_moved_between_categories_is_rejected(self):
        # The totals agree; only the per-category check can see it.
        for src in tb.CATEGORIES:
            for dst in tb.CATEGORIES:
                cost = dict(tb.default_cost("canary"))
                if src == dst or cost.get(src, 0) < 1:
                    continue
                cost[src] -= 1
                cost[dst] = cost.get(dst, 0) + 1
                with self.subTest(src=src, dst=dst):
                    with self.assertRaisesRegex(sc.InvalidAllocation,
                                                "canary " + src + " words"):
                        tb.parsed(work={"canary": cost})

    def test_offsetting_errors_in_other_categories_are_rejected(self):
        # empty and canary differ in rts and interpreter words by opposite
        # amounts: every total and the native words still agree.
        work = {"empty": {"native": 3, "rts": 1},
                "canary": {"native": 3 + sc.CANARY["native"],
                           "interpreter": 1}}
        with self.assertRaisesRegex(sc.InvalidAllocation, "canary rts"):
            tb.parsed(work=work)
        work = {"empty": {"native": 3, "interpreter": 1},
                "canary": {"native": 3 + sc.CANARY["native"], "rts": 1}}
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "canary (rts|interpreter)"):
            tb.parsed(work=work)

    def test_dead_or_underreporting_counter_is_rejected(self):
        dead = {name: {} for name in sc.names(3)}
        with self.assertRaisesRegex(sc.InvalidAllocation, "canary"):
            tb.parsed(work=dead, start=1)
        half = {name: {"native": 1} for name in sc.names(3)}
        with self.assertRaisesRegex(sc.InvalidAllocation, "canary"):
            tb.parsed(work=half)
        with self.assertRaisesRegex(sc.InvalidAllocation, "no startup"):
            tb.parsed(start=0)

    def test_wrong_runtime_in_process_maps(self):
        def stdout(symbol, maps):
            rows = ["@@TASK29_ALLOC_RUNTIME_V1\t" + symbol]
            rows += ["@@TASK29_ALLOC_MAP_V1\t" +
                     "ffff-ffff r-xp 0 00:00 1 " + p for p in maps]
            return "\n".join(rows) + "\n"
        self.assertEqual(sc.check_runtime(stdout(LIB, [LIB, LIB]), LIB)
                         ["symbol"], LIB)
        other = "/usr/lib/libpolyml.so.16"
        self.assertEqual(sc.check_runtime(
            stdout(ALIAS, [LIB]), LIB, [ALIAS])["maps"], [LIB])
        for symbol, maps in ((other, [other]), (LIB, [LIB, other]),
                             (LIB, [other]), (LIB, []), (ALIAS, [LIB])):
            with self.assertRaises(sc.InvalidAllocation):
                sc.check_runtime(stdout(symbol, maps), LIB)
        two = stdout(LIB, [LIB]) + "@@TASK29_ALLOC_RUNTIME_V1\t" + LIB + "\n"
        with self.assertRaises(sc.InvalidAllocation):
            sc.check_runtime(two, LIB)

    def test_a_bracket_present_twice_is_refused(self):
        brackets, _ = tb.parsed()
        with self.assertRaisesRegex(sc.InvalidAllocation, "duplicated"):
            sc.observation(brackets + [brackets[1]], STEADY)
        phases = sc.observation(brackets, STEADY)["phases"]
        self.assertEqual(len(phases["operation_steady"]), 3)

    def test_exact_values_only(self):
        for bad in (1.5, "3", None, True):
            with self.assertRaises(sc.InvalidAllocation):
                sc.exact(bad)
            with self.assertRaises(sc.InvalidAllocation):
                sc.per_run("setup", bad, 1)
        self.assertEqual(sc.exact(Fraction(7, 2)), Fraction(7, 2))
        self.assertEqual(sc.per_run("operation_steady", 7, 2),
                         Fraction(7, 2))
        self.assertEqual(sc.per_run("setup", 7, 2), 7)

    def test_bytes_use_word_field_with_checked_arithmetic(self):
        self.assertEqual(sc.to_bytes(5), 40)
        with self.assertRaises(sc.InvalidAllocation):
            sc.to_bytes(2 ** 61)
        self.assertEqual(sc.to_bytes(2 ** 61 - 1), (2 ** 61 - 1) * 8)


# --------------------------------------------------------------- decisions

def category_cases():
    return [(phase, metric) for phase in sc.PHASES for metric in sc.METRICS]


class Decisions(unittest.TestCase):
    def phase(self, cell, phase="setup", metric="total"):
        return cell["phases"][phase][metric]

    def test_identical_sides_pass(self):
        pairs, control = experiment({}, {})
        cell = an.cell(pairs, control, 4)
        self.assertEqual(set(cell["phases"]), set(an.GATED))
        self.assertEqual(set(an.GATED), {"setup", "operation_first",
                                         "operation_steady", "apply"})
        self.assertTrue(all(len(p) == len(sc.METRICS) and all(
            m["decision"] == "pass" for m in p.values())
            for p in cell["phases"].values()))

    def test_improvement_passes(self):
        pairs, control = experiment({"setup": 10}, {"setup": 9})
        self.assertEqual(self.phase(an.cell(pairs, control, 4))["decision"],
                         "pass")

    def test_every_gated_phase_and_metric_fails_on_one_extra_word(self):
        for phase in sc.PHASES:
            for category in tb.CATEGORIES:
                with self.subTest(phase=phase, category=category):
                    pairs, control = experiment({phase: {}},
                                                {phase: {category: 1}})
                    cell = an.cell(pairs, control, 4)
                    failing = {(p, k) for p, ms in cell["phases"].items()
                               for k, v in ms.items()
                               if v["decision"] == "fail"}
                    want = {category, "total"} | (
                        set() if category == "code" else {"heap"})
                    self.assertEqual(failing, {(phase, k) for k in want})
                    self.assertEqual(set(cell["phases"][phase]),
                                     set(sc.METRICS))

    def test_code_words_are_gated_but_excluded_from_heap(self):
        pairs, control = experiment({}, {"apply": {"code": 2}})
        cell = an.cell(pairs, control, 4)
        self.assertEqual(self.phase(cell, "apply", "code")["decision"],
                         "fail")
        self.assertEqual(self.phase(cell, "apply", "total")["decision"],
                         "fail")
        self.assertEqual(self.phase(cell, "apply", "heap")["decision"],
                         "pass")

    def test_one_extra_word_in_one_pair_fails(self):
        pairs, control = experiment({"setup": 10}, {"setup": 10})
        pairs[7]["candidate"] = observation({"setup": 11})
        cell = an.cell(pairs, control, 4)
        self.assertEqual(self.phase(cell)["decision"], "fail")
        self.assertFalse(self.phase(cell)["deterministic"]["candidate"])

    def test_extra_word_in_one_steady_repeat_fails(self):
        pairs, control = experiment({"operation_steady": [8, 8, 8]},
                                    {"operation_steady": [8, 8, 8]})
        pairs[0]["candidate"] = observation({"operation_steady": [8, 9, 8]})
        cell = an.cell(pairs, control, 4)
        self.assertEqual(self.phase(cell, "operation_steady")["decision"],
                         "fail")

    def test_control_divergence_is_inconclusive_even_for_improvement(self):
        pairs, control = experiment(
            {"setup": 10}, {"setup": 1},
            lambda i: observation({"setup": 10 + (i == 4)}))
        cell = an.cell(pairs, control, 4)
        self.assertEqual(self.phase(cell)["decision"], "inconclusive")
        self.assertFalse(self.phase(cell)["control_identical"])
        # Other rows of the same cell are unaffected.
        self.assertEqual(self.phase(cell, "apply")["decision"], "pass")

    def test_control_checks_every_side_process_and_repeat(self):
        steady = [8, 8, 8]
        base = {"operation_steady": steady}
        for label, side, process, repeat in (
                ("control copy, first process", "control", 0, 0),
                ("control copy, last process", "control", 9, 2),
                ("control baseline, last repeat", "baseline", 9, 2),
                ("control baseline, middle repeat", "baseline", 4, 1)):
            with self.subTest(label):
                pairs, control = experiment(base, base)
                odd = list(steady)
                odd[repeat] = 9
                control[process][side] = observation(
                    {"operation_steady": odd})
                cell = an.cell(pairs, control, 4)
                row = self.phase(cell, "operation_steady")
                self.assertFalse(row["control_identical"])
                self.assertEqual(row["decision"], "inconclusive")

    def test_baseline_drift_in_candidate_pairs_is_not_hidden(self):
        # B = 100 in the candidate pairs, B/B both 90, C = 100: a real +10
        # on the candidate side would otherwise pass as 'control identical'.
        pairs, control = experiment({"setup": 100}, {"setup": 100})
        control = [dict(baseline=observation({"setup": 90}),
                        control=observation({"setup": 90})) for _ in control]
        row = self.phase(an.cell(pairs, control, 4))
        self.assertFalse(row["control_identical"])
        self.assertEqual(row["decision"], "inconclusive")
        # The same drift in one baseline process and one repeat only.
        pairs, control = experiment({"operation_steady": [8, 8, 8]},
                                    {"operation_steady": [8, 8, 8]})
        pairs[6]["baseline"] = observation({"operation_steady": [8, 8, 9]})
        row = self.phase(an.cell(pairs, control, 4), "operation_steady")
        self.assertEqual(row["decision"], "inconclusive")

    def test_reproducible_unequal_steady_repeats_are_deterministic(self):
        steady = {"operation_steady": [9, 8, 8]}
        pairs, control = experiment(steady, steady)
        row = self.phase(an.cell(pairs, control, 4), "operation_steady")
        self.assertEqual(row["decision"], "pass")
        self.assertEqual(row["deterministic"],
                         {"baseline": True, "candidate": True})
        self.assertEqual(row["baseline"], {"2": 20, "9/4": 10})

    def test_processes_that_differ_are_not_deterministic(self):
        pairs, control = experiment({"setup": 10}, {"setup": 10})
        pairs[3]["baseline"] = observation({"setup": 11})
        pairs[3]["candidate"] = observation({"setup": 11})
        row = self.phase(an.cell(pairs, control, 4))
        self.assertEqual(row["deterministic"],
                         {"baseline": False, "candidate": False})

    def test_published_startup_and_empty_are_never_gated(self):
        pairs, control = experiment({"startup": 1}, {"startup": 99})
        cell = an.cell(pairs, control, 4)
        self.assertNotIn("startup", cell["phases"])
        row = cell["published"]["startup"]["total"]
        self.assertEqual(row["candidate"], {"99": 10})
        self.assertEqual(row["difference"], {"98": 10})
        self.assertEqual(row["control_difference"], {"0": 10})
        self.assertEqual(row["bytes"]["candidate"], {"792": 10})
        self.assertEqual(set(cell["published"]), set(sc.PUBLISHED))

    def test_published_control_difference_shows_baseline_drift(self):
        pairs, control = experiment({"startup": 5}, {"startup": 5})
        control = [dict(baseline=observation({"startup": 5}),
                        control=observation({"startup": 6}))
                   for _ in control]
        row = an.cell(pairs, control, 4)["published"]["startup"]["total"]
        self.assertEqual(row["control_difference"], {"1": 10})
        self.assertEqual(row["control"], {"5": 10, "6": 10})

    def test_gated_rows_publish_bytes_next_to_words(self):
        pairs, control = experiment({"setup": 10}, {"setup": 9})
        row = self.phase(an.cell(pairs, control, 4))
        self.assertEqual(row["bytes"], {"baseline": {"80": 10},
                                        "candidate": {"72": 10},
                                        "control": {"80": 20}})

    def test_steady_values_are_exact_per_run_rationals(self):
        pairs, control = experiment({"operation_steady": 7},
                                    {"operation_steady": 7}, steady=2)
        cell = an.cell(pairs, control, 2)
        self.assertEqual(self.phase(cell, "operation_steady")["baseline"],
                         {"7/2": 30})

    def test_cell_needs_an_ab_and_a_ba_pair_and_the_steady_count(self):
        pairs, control = experiment({}, {}, pairs=1)
        with self.assertRaises(sc.InvalidAllocation):
            an.cell(pairs, control, 4)
        pairs, control = experiment({}, {}, pairs=2)
        with self.assertRaises(sc.InvalidAllocation):
            an.cell(pairs, control[:1], 4)
        with self.assertRaises(sc.InvalidAllocation):
            an.cell(pairs, control, 8)

    def sizes(self, base, cand):
        """Cells of one case, values indexed by size, native setup words."""
        cells, data = {}, {}
        for n in a.SIZES:
            pairs, control = experiment({"setup": base[n]}, {"setup": cand[n]})
            cells[n] = an.cell(pairs, control, 4)
            data[n] = (pairs, control)
        return cells, data

    def test_slope_regression_fails_although_cells_pass(self):
        base = dict(zip(a.SIZES, (100, 105, 150, 600, 5100, 50100)))
        cand = {**base, 0: 50, 1: 104, 10: 140}
        cells, data = self.sizes(base, cand)
        self.assertTrue(all(c["phases"]["setup"]["total"]["decision"] ==
                            "pass" for c in cells.values()))
        rows = an.slopes(cells, list(a.SIZES), data)["setup"]["total"]
        self.assertEqual(rows[0]["decision"], "fail")
        self.assertEqual(rows[0]["baseline"], {"5": 10})
        self.assertEqual(rows[0]["candidate"], {"54": 10})
        # Slope below, above, then equal to the baseline's.
        self.assertEqual([r["decision"] for r in rows],
                         ["fail", "pass", "fail", "pass", "pass"])
        self.assertEqual(rows[1]["candidate"], {"4": 10})
        self.assertEqual(rows[2]["candidate"], {"46/9": 10})

    def test_a_size_specific_improvement_fails_on_the_adjacent_slope(self):
        base = dict.fromkeys(a.SIZES, 100)
        cand = {**base, 1000: 50}
        cells, data = self.sizes(base, cand)
        rows = an.slopes(cells, list(a.SIZES), data)["setup"]["total"]
        self.assertEqual([r["decision"] for r in rows],
                         ["pass", "pass", "pass", "pass", "fail"])

    def test_slopes_compare_every_process_not_only_the_first(self):
        base = dict.fromkeys(a.SIZES, 10)
        cells, data = self.sizes(base, base)
        pairs, control = data[10000]
        pairs[7] = dict(pairs[7], candidate=observation({"setup": 11}))
        data[10000] = (pairs, control)
        rows = an.slopes(cells, list(a.SIZES), data)["setup"]["total"]
        self.assertEqual(rows[-1]["decision"], "fail")
        self.assertEqual(rows[-1]["candidate"], {"0": 9, "1/9000": 1})

    def test_slopes_cover_every_gated_phase_and_metric(self):
        base = dict.fromkeys(a.SIZES, 10)
        cells, data = self.sizes(base, base)
        slopes = an.slopes(cells, list(a.SIZES), data)
        self.assertEqual(set(slopes), set(an.GATED))
        self.assertTrue(all(set(v) == set(sc.METRICS) and all(
            len(rows) == 5 for rows in v.values())
            for v in slopes.values()))

    def test_sizes_measured_with_different_repeat_layouts_are_refused(self):
        base = dict.fromkeys(a.SIZES, 10)
        cells, data = self.sizes(base, base)
        pairs, control = data[10]
        longer = observation({"setup": 10, "operation_steady": [1, 1, 1, 1]})
        data[10] = ([dict(p, baseline=longer) for p in pairs], control)
        with self.assertRaisesRegex(sc.InvalidAllocation, "repeat layout"):
            an.slopes(cells, list(a.SIZES), data)

    def test_exact_non_integer_slopes(self):
        base = dict(zip(a.SIZES, (0, 1, 2, 3, 4, 5)))
        cells, data = self.sizes(base, base)
        rows = an.slopes(cells, list(a.SIZES), data)["setup"]["total"]
        self.assertEqual([r["baseline"] for r in rows],
                         [{"1": 10}, {"1/9": 10}, {"1/90": 10},
                          {"1/900": 10}, {"1/9000": 10}])

    def test_slopes_inconclusive_when_either_control_diverges(self):
        base = dict(zip(a.SIZES, (1, 2, 3, 4, 5, 6)))
        cells, data = self.sizes(base, base)
        pairs, control = experiment(
            {"setup": 3}, {"setup": 3},
            lambda i: observation({"setup": 3 + (i == 0)}))
        cells[10] = an.cell(pairs, control, 4)
        rows = an.slopes(cells, list(a.SIZES), data)["setup"]["total"]
        self.assertEqual([r["decision"] for r in rows],
                         ["pass", "inconclusive", "inconclusive", "pass",
                          "pass"])

    def test_constants_are_the_size_zero_cell(self):
        base = dict.fromkeys(a.SIZES, 10)
        cand = {**base, 0: 11}
        cells, _ = self.sizes(base, cand)
        constant = an.constants(cells)["setup"]["total"]
        self.assertEqual(constant["decision"], "fail")
        self.assertEqual((constant["baseline"], constant["candidate"]),
                         ({"10": 10}, {"11": 10}))

    def test_status_precedence_has_no_allowance(self):
        self.assertEqual(an.status(["pass", "pass"]), "pass")
        self.assertEqual(an.status(["pass", "inconclusive"]), "inconclusive")
        self.assertEqual(an.status(["inconclusive", "fail"]), "fail")
        self.assertEqual(an.status([]), "inconclusive")

    def test_case_decisions_include_cells_and_slopes(self):
        base = dict(zip(a.SIZES, (100, 105, 150, 600, 5100, 50100)))
        cells, data = self.sizes(base, base)
        record = dict(cells=cells, slopes=an.slopes(cells, list(a.SIZES),
                                                    data))
        found = an.case_decisions(record)
        self.assertEqual(len(found), 6 * 4 * 6 + 5 * 4 * 6)
        record["slopes"]["setup"]["total"][2]["decision"] = "fail"
        self.assertIn("fail", an.case_decisions(record))
        record["slopes"]["setup"]["total"][2]["decision"] = "pass"
        cells[100]["phases"]["apply"]["heap"]["decision"] = "fail"
        self.assertIn("fail", an.case_decisions(record))


# --------------------------------------------------------- archived cells

def build_for(experiment_, side_, pair_, **change):
    """build() hook changing receipt() of exactly one archived process."""
    def build(experiment, side, pair):
        if (experiment, side, pair) == (experiment_, side_, pair_):
            return change
    return build


def tamper_path(experiment="candidate", side="candidate", pair=1):
    return "%s/pair-%02d-%s.json.gz" % (experiment, pair, m.SIDES[side])


def find_event(events, kind, nth=0):
    return [i for i, e in enumerate(events) if e[0] == kind][nth]


def drop(*kinds_and_values):
    def change(events):
        for kind, value in kinds_and_values:
            events[:] = [e for e in events if e[:2] != [kind, value]]
    return change


def mut_header(events):
    events[0][1] = m.SIDES["baseline"]


def mut_cwd(events):
    events[1][1] = "/elsewhere"


def mut_holdir(events):
    events[2] = ["holdir", "/other", "/other"]


def mut_preloaded_missing(events):
    events[3] = ["preloaded"]


def mut_preloaded_selected(events):
    events[3] = ["preloaded", "Lib,Traverse"]


def mut_no_heap(events):
    del events[find_event(events, "heapfile")]


def mut_duplicate_heap(events):
    events.insert(5, list(events[4]))


def mut_bad_heap(events):
    events[4] = ["heapfile"]


def mut_search_private(events):
    events[5] = ["search", "/elsewhere"]


def mut_search_sigobj(events):
    events[6] = ["search", "/elsewhere/sigobj"]


def mut_end_count(events):
    events[-1] = ["end", "pass", "2"]


def mut_end_error(events):
    events[-1] = ["end", "error", "1"]


def mut_reuse(events):
    events.insert(find_event(events, "use") + 1, ["use", "/x.sml"])


def mut_unmatched_used(events):
    events[find_event(events, "used")] = ["used", "/x.sml"]


def mut_observation_late(events):
    i = find_event(events, "loaded")
    j = find_event(events, "observation")
    events.insert(j, events.pop(i))


def mut_bad_loaded(events):
    events[find_event(events, "loaded")] = ["loaded"]


def mut_dup_loaded(events):
    i = find_event(events, "loaded")
    events.insert(i, list(events[i]))


def mut_unknown(events):
    events.insert(find_event(events, "loaded"), ["bogus", "x"])


def mut_pending(events):
    events.insert(find_event(events, "loaded"), ["use", "/x.sml"])


def mut_other_kind_at_preloaded(events):
    events[3] = ["cwd", "x"]


def mut_loaded_inventory_short(events):
    i = [n for n, e in enumerate(events) if e[0] == "loaded" and
         e[1].endswith("Performance.sml")][0]
    del events[i]


def rec_declare_pending_path(record):
    # So that only the unfinished `use` itself can be noticed.
    record["paths"]["/x.sml"] = next(iter(record["paths"].values()))


def mut_use_after_loaded(events):
    i = max(n for n, e in enumerate(events) if e[0] == "loaded")
    events[i + 1:i + 1] = [["use", "/y.sml"], ["used", "/y.sml"]]


def mut_used_after_loaded(events):
    first = min(n for n, e in enumerate(events) if e[0] == "loaded")
    events.insert(first, ["use", "/y.sml"])
    last = max(n for n, e in enumerate(events) if e[0] == "loaded")
    events.insert(last + 1, ["used", "/y.sml"])


def mut_use_extra_field(events):
    events.insert(find_event(events, "loaded"), ["use", "/y.sml", "x"])


def mut_used_extra_field(events):
    i = find_event(events, "used")
    events[i] = events[i] + ["x"]


def mut_no_support(events):
    events[:] = [e for e in events if not (
        e[0] in ("use", "used", "loaded") and
        e[1].endswith("MatrixSupport.sml"))]


def mut_no_perf(events):
    events[:] = [e for e in events if not (
        e[0] in ("use", "used", "loaded") and
        e[1].endswith("Performance.sml"))]


def mut_without(name):
    def mutate(events):
        events[:] = [e for e in events if not (
            e[0] in ("use", "used", "loaded") and
            e[1].endswith("/" + name))]
    return mutate


def rec_set(**fields):
    def change(record):
        record.update(fields)
    return change


def rec_env(key, value):
    def change(record):
        if value is None:
            del record["environment"][key]
        else:
            record["environment"][key] = value
    return change


def rec_path(suffix, **fields):
    def change(record):
        for raw, info in record["paths"].items():
            if raw.endswith(suffix):
                info.update(fields)
    return change


def rec_drop_path(suffix):
    def change(record):
        for raw in [r for r in record["paths"] if r.endswith(suffix)]:
            del record["paths"][raw]
    return change


def rec_extra_path(record):
    record["paths"]["/x.sml"] = dict(record["paths"][
        next(iter(record["paths"]))])


def rec_stdout(old, new):
    def change(record):
        record["stdout"] = record["stdout"].replace(old, new)
    return change


def rec_rename_private(record):
    for raw, info in record["paths"].items():
        if raw.endswith("Traverse.sml"):
            info["physical"] = info["physical"].replace("Traverse.sml",
                                                        "Bar.sml")


def rec_sha(suffix):
    return rec_path(suffix, sha256="0" * 64)


def rec_product(record):
    for info in record["paths"].values():
        for product in info["related_products"]:
            info["related_products"][product]["bytes"] += 1


def rec_logical(suffix, name):
    """The path loaded by another name (`@REPO@` stands for the toolchain),
    the file it is, and its products unchanged."""
    def change(record):
        for raw in [r for r in record["paths"] if r.endswith(suffix)]:
            new = name.replace("@REPO@", str(Path(raw).parents[1]))
            record["paths"][new] = record["paths"].pop(raw)
            record["stdout"] = record["stdout"].replace(raw, new)
    return change


def rec_related(suffix, product):
    """An extra related product (a file beside the source) of a path."""
    def change(record):
        for raw, info in record["paths"].items():
            if raw.endswith(suffix):
                info["related_products"][product] = dict(
                    sha256="1" * 64, bytes=1)
    return change


def meta_set(**fields):
    def change(meta):
        meta.update(fields)
    return change


# (label, build kwargs, receipt change, meta change, regex); the process
# tampered with is candidate/candidate/pair 1 unless built otherwise.
CELL_GUARDS = [
    ("rejected process", {}, rec_set(accepted=False), None, "failed"),
    ("process exit", {}, rec_set(exit=1), None, "failed"),
    ("process timeout", {}, rec_set(timed_out=True), None, "failed"),
    ("process accepted missing", {}, lambda r: r.pop("accepted"), None,
     "malformed"),
    ("side outside experiment", {},
     rec_set(side="control", selection=m.SIDES["control"]), None,
     "selection"),
    ("experiment field", {}, rec_set(experiment="control"), None,
     "selection"),
    ("selection label", {}, rec_set(selection="candidate"), None,
     "selection"),
    ("pair beyond count", {}, rec_set(pair=99), None, "pair index"),
    ("negative pair", {}, rec_set(pair=-1), None, "pair index"),
    ("float pair index", {}, rec_set(pair=1.0), None, "pair index"),
    ("order flipped", {}, rec_set(position=1), None, "AB/BA"),
    ("env case", {}, rec_env("PERF_CASE", "frag_named"), None, "environment"),
    ("env size", {}, rec_env("PERF_SIZE", "10"), None, "environment"),
    ("env steady", {}, rec_env("ALLOC_STEADY", "5"), None, "environment"),
    ("env repeats", {}, rec_env("ALLOC_REPEATS", "4"), None, "environment"),
    ("env library", {}, rec_env("LD_LIBRARY_PATH", "/usr/lib"), None,
     "environment"),
    ("env private name", {}, rec_env("PAIR_PRIVATE", "/x/sel-b0"), None,
     "environment"),
    ("env target", {}, rec_env("PAIR_TARGET", "Other"), None,
     "environment"),
    ("env fixture", {}, rec_env("PAIR_FIXTURE", "signature"), None,
     "environment"),
    ("env control", {}, rec_env("PAIR_CONTROL", "x"), None, "environment"),
    ("env selection", {}, rec_env("PAIR_SELECTION", "baseline"), None,
     "environment"),
    ("env shim", {}, rec_env("TASK29_ALLOC_SHIM", "/other.so"), None,
     "environment"),
    ("env extra key", {}, rec_env("PERF_EXTRA", "1"), None, "environment"),
    ("env unrelated extra variable", {}, rec_env("UNRELATED_EXTRA", "1"),
     None, "environment"),
    ("env base compiler", {}, rec_env("CC", "/other/cc"), None,
     "environment"),
    ("env base HOME", {}, rec_env("HOME", "/root"), None, "environment"),
    ("env base PATH", {}, rec_env("PATH", "/usr/bin"), None, "environment"),
    ("env base PATH of the caller", {},
     rec_env("PATH", "/home/x/.local/bin:" + m.pr.PATH), None, "environment"),
    ("env place TMPDIR", {}, rec_env("TMPDIR", "/elsewhere"), None,
     "environment"),
    ("env place TMPDIR missing", {}, rec_env("TMPDIR", None), None,
     "environment"),
    ("env toolchain HOLDIR", {}, rec_env("HOLDIR", "/other/hol"), None,
     "environment"),
    ("env base key missing", {}, rec_env("TZ", None), None, "environment"),
    ("env base key extra", {}, rec_env("LD_PRELOAD", "/x.so"), None,
     "environment"),
    ("env missing key", {}, rec_env("PERF_SIZE", None), None,
     "environment"),
    ("loader header label", dict(mutate=mut_header), None, None,
     "loader header"),
    ("loader cwd", dict(mutate=mut_cwd), None, None, "loader header"),
    ("loader holdir", dict(mutate=mut_holdir), None, None, "loader header"),
    ("preloaded missing", dict(mutate=mut_preloaded_missing), None, None,
     "preloaded"),
    ("preloaded selected", dict(mutate=mut_preloaded_selected), None, None,
     "preloaded in shared heap"),
    ("no heap inventory", dict(mutate=mut_no_heap), None, None,
     "heap inventory"),
    ("duplicate heap inventory", dict(mutate=mut_duplicate_heap), None, None,
     "heap inventory"),
    ("invalid heap inventory", dict(mutate=mut_bad_heap), None, None,
     "heap inventory"),
    ("search private", dict(mutate=mut_search_private), None, None,
     "search paths"),
    ("search sigobj", dict(mutate=mut_search_sigobj), None, None,
     "search paths"),
    ("end count", dict(mutate=mut_end_count), None, None, "completion"),
    ("end error", dict(mutate=mut_end_error), None, None, "completion"),
    ("use while pending", dict(mutate=mut_reuse), None, None,
     "unordered archived source use"),
    ("unmatched used", dict(mutate=mut_unmatched_used), None, None,
     "unmatched"),
    ("observation after loaded", dict(mutate=mut_observation_late), None,
     None, "after loaded"),
    ("invalid loaded", dict(mutate=mut_bad_loaded), None, None,
     "invalid loaded"),
    ("duplicate loaded", dict(mutate=mut_dup_loaded), None, None,
     "incomplete archived source inventory"),
    ("unknown event", dict(mutate=mut_unknown), None, None,
     "unknown archived event"),
    ("use after the loaded inventory", dict(mutate=mut_use_after_loaded),
     None, None, "unordered archived source use"),
    ("use with an extra field", dict(mutate=mut_use_extra_field), None,
     None, "unordered archived source use"),
    ("completion after the loaded inventory",
     dict(mutate=mut_used_after_loaded), None, None,
     "unmatched archived source completion"),
    ("completion with an extra field", dict(mutate=mut_used_extra_field),
     None, None, "unmatched archived source completion"),
    ("pending source", dict(mutate=mut_pending), None, None,
     "incomplete archived source inventory"),
    ("pending source with its path listed", dict(mutate=mut_pending),
     rec_declare_pending_path, None, "incomplete archived source inventory"),
    ("other event where the preloaded inventory belongs",
     dict(mutate=mut_other_kind_at_preloaded), None, None, "preloaded"),
    ("completed source missing from the loaded inventory",
     dict(mutate=mut_loaded_inventory_short), None, None,
     "incomplete archived source inventory"),
    ("extra path", {}, rec_extra_path, None,
     "incomplete archived source inventory"),
    ("missing path", {}, rec_drop_path("Traverse.sml"), None,
     "incomplete archived source inventory"),
    ("selected Traverse never elaborated",
     dict(mutate=mut_without("Traverse.sml")), rec_drop_path("Traverse.sml"),
     None, "selected implementation not elaborated: Traverse"),
    ("selected simpLib never elaborated",
     dict(mutate=mut_without("simpLib.sml")), rec_drop_path("simpLib.sml"),
     None, "selected implementation not elaborated: simpLib"),
    ("fixture support never completed",
     dict(mutate=mut_no_support), rec_drop_path("MatrixSupport.sml"), None,
     "fixture never completed"),
    ("fixture performance never completed",
     dict(mutate=mut_no_perf), rec_drop_path("Performance.sml"), None,
     "fixture never completed: Performance.sml"),
    ("runtime elsewhere", {}, rec_stdout(LIB, "/usr/lib/libpolyml.so.16"),
     None, "runtime"),
    ("selected source changed", {}, rec_sha("Traverse.sml"), None,
     "wrong selected source: Traverse.sml"),
    ("selected source renamed", {}, rec_rename_private, None,
     "wrong selected source: Bar.sml"),
    ("fixture changed", {}, rec_sha("Performance.sml"), None,
     "wrong selected source: Performance.sml"),
    ("support fixture changed", {}, rec_sha("MatrixSupport.sml"), None,
     "wrong selected source: MatrixSupport.sml"),
    ("shared input outside toolchain", {},
     rec_path("Heap1.sml", physical="/elsewhere/Heap1.sml"), None,
     "outside the toolchain"),
    ("shared simplifier leaked", {},
     rec_path("Heap1.sml", physical="@REPO@/src/simp/Heap1.sml"), None,
     "outside the toolchain"),
    ("shared input under a boundary prefix", {},
     rec_path("Heap1.sml", physical="@REPO@/src/boss/Heap1.sml"), None,
     "boundary prefix src/boss/"),
    ("shared input under another boundary prefix", {},
     rec_path("Heap1.sml", physical="@REPO@/help/Docfiles/a/Heap1.sml"),
     None, "boundary prefix help/Docfiles/"),
    ("shared product under a boundary prefix", {},
     rec_related("Heap1.sml", "@REPO@/src/boss/bossLib.uo"), None,
     "boundary prefix src/boss/"),
    ("shared product outside the toolchain", {},
     rec_related("Heap1.sml", "/elsewhere/bossLib.uo"), None,
     "outside the toolchain: /elsewhere/bossLib.uo"),
    ("loaded by a name under a boundary prefix", {},
     rec_logical("Heap1.sml", "@REPO@/src/boss/Heap1.sml"), None,
     "boundary prefix src/boss/: .*/src/boss/Heap1.sml"),
    ("loaded by a name under a prefix through a dotdot", {},
     rec_logical("Heap1.sml", "@REPO@/src/x/../boss/Heap1.sml"), None,
     "boundary prefix src/boss/"),
    ("loaded by a name outside the toolchain", {},
     rec_logical("Heap1.sml", "/elsewhere/Heap1.sml"), None,
     "outside the toolchain: /elsewhere/Heap1.sml"),
    ("shared input differs", {}, rec_sha("Heap1.sml"), None,
     "shared input changed"),
    ("shared product differs", {}, rec_product, None,
     "shared input changed"),
    ("cell rejected", {}, None, meta_set(rejected="boom"), "unresolved"),
    ("cell schema", {}, None, meta_set(schema="other"), "different inputs"),
] + [("cell binding " + key, {}, None, meta_set(**{key: value}),
      "different inputs") for key, value in (
    ("case", "frag_named"), ("size", 10), ("steady", 5), ("repeats", 4),
    ("pairs", 3), ("library", "/other.so"), ("aliases", []),
    ("repo", "/other"), ("shim", "/other.so"), ("word_bytes", 4),
    ("environment", {}), ("tmpdir", "/other"),
    ("boundary_prefixes", []),
    ("sources", {}), ("revisions", {}), ("fixtures", {}),
    ("grid", "0" * 64))]


class Replay(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.sb = tb.Sandbox(self.tmp.name)

    def archive(self, build=None, **kw):
        return self.sb.archive(self.tmp.name, build, **kw)

    def analyze(self, build=None, **kw):
        out = self.archive(build, **kw)
        return m.replay_cell(out, self.sb.bind())["record"]

    def test_archive_replays_to_pass(self):
        cell = self.analyze()
        self.assertEqual(m.cell_status(cell), "pass")
        self.assertEqual(cell["pairs"], 10)
        # the canary's known words, on top of the no-op bracket's four
        self.assertEqual(
            cell["published"]["canary"]["native"]["baseline"],
            {str(sc.CANARY["native"] + 4): 10})

    def test_candidate_plus_one_word_fails_after_replay(self):
        cell = self.analyze(build_for("candidate", "candidate", 3,
                                      work={"apply": {"native": 4}}))
        self.assertEqual(cell["phases"]["apply"]["total"]["decision"],
                         "fail")
        self.assertEqual(cell["phases"]["apply"]["total"]["difference"],
                         {"0": 9, "1": 1})

    def test_baseline_control_divergence_is_inconclusive(self):
        cell = self.analyze(build_for("control", "control", 1,
                                      work={"setup": {"native": 4}}))
        self.assertEqual(cell["phases"]["setup"]["total"]["decision"],
                         "inconclusive")

    def test_baseline_drift_in_candidate_pairs_is_inconclusive(self):
        def build(experiment, side, pair):
            if experiment == "candidate":
                return dict(work={"setup": {"native": 6}})
        cell = self.analyze(build)
        row = cell["phases"]["setup"]["total"]
        self.assertEqual((row["baseline"], row["candidate"], row["control"]),
                         ({"6": 10}, {"6": 10}, {"3": 20}))
        self.assertEqual(row["decision"], "inconclusive")

    def test_cell_data_guard_table(self):
        for label, kwargs, change, meta_change, message in CELL_GUARDS:
            with self.subTest(label):
                tmp = Path(self.tmp.name) / ("guard-" + label.replace(
                    " ", "-"))
                sb = tb.Sandbox(tmp, pairs=4)
                folder = tmp / "cell"
                sb.write_cell(folder, build_for("candidate", "candidate",
                                                1, **kwargs))
                if change:
                    path = folder / tamper_path()
                    record = a.load(path)
                    change(record)
                    record = json.loads(json.dumps(record).replace(
                        "@REPO@", str(sb.repo)))
                    path.unlink()
                    m.write_receipt(path.parent, path.name[:-8], record)
                if meta_change:
                    meta = a.load(folder / "meta.json.gz")
                    meta_change(meta)
                    (folder / "meta.json.gz").unlink()
                    m.write_receipt(folder, "meta", meta)
                with self.assertRaisesRegex(sc.InvalidAllocation, message):
                    m.cell_data(folder, sb.bind())

    def test_a_name_is_judged_as_normalized(self):
        # not under src/boss/ although the name passes through it
        for name in ("@REPO@/src/boss/../Heap1.sml",
                     "@REPO@/src/./Heap1.sml"):
            with self.subTest(name):
                sb = tb.Sandbox(Path(self.tmp.name) / ("n%d" % len(name)),
                                pairs=4)
                folder = Path(sb.root) / "cell"
                sb.write_cell(folder)
                for path in folder.rglob("pair-*.json.gz"):
                    tb.rewrite(path, rec_logical("Heap1.sml", name))
                self.assertEqual(m.cell_data(folder, sb.bind())[0]["pairs"],
                                 4)

    def test_missing_extra_and_duplicate_processes_rejected(self):
        sb = tb.Sandbox(Path(self.tmp.name) / "p", pairs=4)
        folder = Path(self.tmp.name) / "p-cell"
        sb.write_cell(folder)
        self.assertEqual(m.cell_data(folder, sb.bind())[0]["pairs"], 4)
        copy = folder / "control" / "pair-03-sel-b1.json.gz"
        extra = folder / "control" / "pair-09-sel-b1.json.gz"
        extra.write_bytes(copy.read_bytes())
        with self.assertRaisesRegex(sc.InvalidAllocation, "missing process"):
            m.cell_data(folder, sb.bind())
        extra.unlink()
        copy.unlink()
        with self.assertRaisesRegex(sc.InvalidAllocation, "missing process"):
            m.cell_data(folder, sb.bind())
        copy.write_bytes((folder / "control" /
                          "pair-03-sel-b0.json.gz").read_bytes())
        with self.assertRaisesRegex(sc.InvalidAllocation, "duplicate"):
            m.cell_data(folder, sb.bind())

    def test_control_must_be_a_copy_of_the_baseline(self):
        sb = tb.Sandbox(Path(self.tmp.name) / "c", pairs=4)
        for key in ("sources", "revisions"):
            with self.subTest(key):
                header = sb.header()
                value = dict(header[key])
                value["control"] = value["candidate"]
                folder = Path(self.tmp.name) / ("copy-" + key)
                sb.write_cell(folder, **{key: value})
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "copy of the baseline"):
                    m.cell_data(folder, sb.bind(**{key: value}))

    def test_malformed_archive_is_a_rejection_not_a_crash(self):
        tmp = Path(self.tmp.name) / "broken"
        sb = tb.Sandbox(tmp, pairs=4)
        sb.write_cell(tmp / "cell")
        tb.rewrite(tmp / "cell" / tamper_path(), lambda r: r.pop("paths"))
        archive = tmp / "broken.json.xz"
        m.bundle.pack(tmp / "cell", archive)
        with self.assertRaisesRegex(sc.InvalidAllocation, "malformed"):
            m.replay_cell(archive, sb.bind())

    def test_malformed_kinds_are_all_rejections(self):
        def listed_paths(record):  # right keys, wrong type
            record["paths"] = list(record["paths"])
        kinds = (("missing field", lambda r: r.pop("paths")),
                 ("wrong type", lambda r: r.__setitem__("environment",
                                                        None)),
                 ("index", lambda r: r.__setitem__("position", 7)),
                 ("attribute", listed_paths))
        for label, change in kinds:
            with self.subTest(label):
                tmp = Path(self.tmp.name) / ("kind-" + label.replace(
                    " ", "-"))
                sb = tb.Sandbox(tmp, pairs=4)
                sb.write_cell(tmp / "cell")
                tb.rewrite(tmp / "cell" / tamper_path(), change)
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "malformed"):
                    m.cell_data(tmp / "cell", sb.bind())

    def test_smoke_pair_count_never_passes(self):
        sb = tb.Sandbox(Path(self.tmp.name) / "s", pairs=2)
        out = sb.archive(Path(self.tmp.name) / "s", name="smoke")
        cell = m.replay_cell(out, sb.bind())["record"]
        decisions = m.assemble({(CASE, 0)}, {(CASE, 0): cell}, {})
        self.assertFalse(decisions["acceptance_pairs"])
        self.assertEqual(decisions["status"], "inconclusive")

    def test_reproducible_unequal_steady_repeats_do_not_downgrade(self):
        def build(experiment, side, pair):
            return dict(work={"operation_steady": [
                {"native": 9}, {"native": 8}, {"native": 8}]})
        cell = self.analyze(build)
        decisions = m.assemble({(CASE, 0)}, {(CASE, 0): cell}, {})
        self.assertEqual(decisions["nondeterminism"], [])
        self.assertEqual(m.cell_status(cell), "pass")

    def test_nondeterminism_is_reported(self):
        cell = self.analyze(build_for("candidate", "candidate", 3,
                                      work={"apply": {"native": 2}}))
        decisions = m.assemble({(CASE, 0)}, {(CASE, 0): cell}, {})
        self.assertIn([CASE, 0, "apply", "total", "candidate"],
                      decisions["nondeterminism"])
        self.assertNotIn([CASE, 0, "apply", "total", "baseline"],
                         decisions["nondeterminism"])

    def test_code_visible_is_listed(self):
        def build(experiment, side, pair):
            if side == "candidate":
                return dict(work={"setup": {"native": 3, "code": 5}})
        cell = self.analyze(build)
        decisions = m.assemble({(CASE, 0)}, {(CASE, 0): cell}, {})
        self.assertIn([CASE, 0, "setup"], decisions["code_visible"])
        self.assertIn(CASE, m.results_markdown(decisions))

    def test_published_varying_rows_are_listed(self):
        cell = self.analyze(build_for("candidate", "candidate", 2,
                                      start=1007))
        decisions = m.assemble({(CASE, 0)}, {(CASE, 0): cell}, {})
        self.assertIn([CASE, 0, "startup", "total", "candidate"],
                      decisions["published_varying"])


# ---------------------------------------------------------- decision files

_TEMPLATE = {}


def template(pairs=10):
    """Identical baseline/candidate in every one of the 162 cells."""
    if pairs not in _TEMPLATE:
        cells, records, observed = set(), {}, {}
        for key in m.keys():
            data = experiment({"setup": 10}, {"setup": 10}, pairs=pairs)
            cells.add(key)
            records[key] = dict(an.cell(*data, STEADY), steady=STEADY,
                                pairs=pairs)
            observed[key] = data
        _TEMPLATE[pairs] = (cells, records, observed)
    cells, records, observed = _TEMPLATE[pairs]
    return set(cells), dict(records), dict(observed)


def regrid(records, observed, case, base, cand, ctrl=None, pairs=10):
    """Replace the cells of one case; base/cand map size to setup words."""
    for size in a.SIZES:
        data = experiment({"setup": base[size]}, {"setup": cand[size]}, ctrl,
                          pairs=pairs)
        records[case, size] = dict(an.cell(*data, STEADY), steady=STEADY,
                                   pairs=pairs)
        observed[case, size] = data


class FullGrid(unittest.TestCase):
    def test_identical_grid_is_complete_and_passes(self):
        out = m.assemble(*template())
        self.assertEqual((out["status"], out["complete"],
                          out["acceptance_pairs"]), ("pass", True, True))
        self.assertEqual(len(out["cases"]), 27)
        self.assertTrue(all(r["slopes"] is not None and
                            r["constants"] is not None and
                            len(r["cells"]) == 6
                            for r in out["cases"].values()))
        self.assertEqual((out["unresolved"], out["nondeterminism"]),
                         ([], []))
        self.assertEqual(m.status_code(out), 0)
        adjacent = [[lo, hi] for lo, hi in zip(a.SIZES, a.SIZES[1:])]
        for record in out["cases"].values():
            for phase in record["slopes"].values():
                for rows in phase.values():
                    self.assertEqual([r["sizes"] for r in rows], adjacent)

    def test_one_failing_cell_fails_the_grid(self):
        cells, records, observed = template()
        key = ("frag_ac", 100)
        data = experiment({"setup": 10}, {"setup": 11})
        records[key] = dict(an.cell(*data, STEADY), steady=STEADY, pairs=10)
        out = m.assemble(cells, records, observed)
        self.assertEqual((out["status"], out["complete"]), ("fail", True))
        self.assertEqual(m.status_code(out), 1)

    def test_a_passing_cell_set_with_a_failing_slope_fails_the_grid(self):
        cells, records, observed = template()
        base = dict(zip(a.SIZES, (100, 105, 150, 600, 5100, 50100)))
        regrid(records, observed, "frag_ac", base,
               {**base, 0: 50, 1: 104, 10: 140})
        self.assertTrue(all(records["frag_ac", n]["phases"]["setup"]["total"]
                            ["decision"] == "pass" for n in a.SIZES))
        out = m.assemble(cells, records, observed)
        self.assertEqual(out["status"], "fail")
        slope = out["cases"]["frag_ac"]["slopes"]["setup"]["total"][0]
        self.assertEqual(slope["decision"], "fail")

    def test_a_failing_cell_with_passing_slopes_fails_the_grid(self):
        cells, records, observed = template()
        base = dict.fromkeys(a.SIZES, 10)
        regrid(records, observed, "frag_ac", base, {**base, 10: 11})
        out = m.assemble(cells, records, observed)
        self.assertEqual(out["status"], "fail")

    def test_one_short_cell_means_no_acceptance_pairs(self):
        cells, records, observed = template()
        records["frag_ac", 10] = dict(records["frag_ac", 10], pairs=9)
        out = m.assemble(cells, records, observed)
        self.assertEqual((out["acceptance_pairs"], out["status"]),
                         (False, "inconclusive"))

    def test_only_the_pinned_baseline_can_pass(self):
        out = m.assemble(*template())
        self.assertTrue(out["acceptance_baseline"])
        for baseline in ("d" * 40, tb.BASE_PIN, ""):
            with self.subTest(baseline):
                out = m.assemble(*template(), baseline=baseline)
                self.assertFalse(out["acceptance_baseline"])
                self.assertTrue(out["complete"] and out["acceptance_pairs"])
                self.assertEqual(out["status"], "inconclusive")
                self.assertEqual(m.status_code(out), 2)

    def test_another_baseline_still_reports_a_definite_failure(self):
        cells, records, observed = template()
        data = experiment({"setup": 10}, {"setup": 11})
        records["frag_ac", 100] = dict(an.cell(*data, STEADY), steady=STEADY,
                                       pairs=10)
        out = m.assemble(cells, records, observed, baseline="d" * 40)
        self.assertEqual((out["status"], out["acceptance_baseline"]),
                         ("fail", False))

    def test_finish_judges_the_baseline_of_the_inventory(self):
        with tempfile.TemporaryDirectory() as tmp:
            sb = tb.Sandbox(tmp)
            root = Path(tmp) / "grid"
            root.mkdir()
            shutil.copyfile(sb.controls_path, root / "controls-receipt.json")
            inventory = dict(sb.header(), jobs=[1], runs=[])
            self.assertFalse(  # the sandbox's baseline is invented
                m.finish(root, inventory)["acceptance_baseline"])
            pinned = dict(inventory, baseline=a.BASE)
            self.assertTrue(m.finish(root, pinned)["acceptance_baseline"])

    def test_missing_case_or_size_means_incomplete_never_pass(self):
        cells, records, observed = template()
        without_case = {k for k in cells if k[0] != "frag_ac"}
        out = m.assemble(without_case, records, observed)
        self.assertEqual((out["status"], out["complete"]),
                         ("inconclusive", False))
        without_size = cells - {("frag_ac", 1000)}
        out = m.assemble(without_size, records, observed)
        self.assertEqual((out["status"], out["complete"]),
                         ("inconclusive", False))
        self.assertIsNone(out["cases"]["frag_ac"]["slopes"])
        self.assertEqual(m.status_code(out), 2)

    def test_smoke_grid_is_complete_but_never_a_pass(self):
        out = m.assemble(*template(2))
        self.assertEqual((out["complete"], out["acceptance_pairs"],
                          out["status"]), (True, False, "inconclusive"))

    def test_unresolved_cell_is_inconclusive(self):
        cells, records, observed = template()
        records["frag_ac", 10] = None
        out = m.assemble(cells, records, observed)
        self.assertEqual((out["status"], out["complete"], out["unresolved"]),
                         ("inconclusive", False, ["frag_ac-10"]))

    def test_a_failure_is_reported_next_to_an_unresolved_cell(self):
        cells, records, observed = template()
        records["frag_ac", 10] = None
        data = experiment({"setup": 10}, {"setup": 11})
        records["frag_create", 0] = dict(an.cell(*data, STEADY),
                                         steady=STEADY, pairs=10)
        out = m.assemble(cells, records, observed)
        self.assertEqual((out["status"], out["complete"]), ("fail", False))

    def test_nondeterminism_downgrades_a_pass_but_not_a_fail(self):
        cells, records, observed = template()
        base = dict.fromkeys(a.SIZES, 10)

        def alternate(i):
            return observation({"setup": 10})
        data = experiment({"setup": 10}, {"setup": 9}, alternate)
        data[0][3]["candidate"] = observation({"setup": 10})
        records["frag_ac", 10] = dict(an.cell(*data, STEADY), steady=STEADY,
                                      pairs=10)
        regrid(records, observed, "frag_ac", base, base)
        records["frag_ac", 10] = dict(an.cell(*data, STEADY), steady=STEADY,
                                      pairs=10)
        out = m.assemble(cells, records, observed)
        self.assertIn(["frag_ac", 10, "setup", "total", "candidate"],
                      out["nondeterminism"])
        self.assertEqual(out["status"], "inconclusive")
        data = experiment({"setup": 10}, {"setup": 11})
        data[0][3]["candidate"] = observation({"setup": 12})
        records["frag_ac", 10] = dict(an.cell(*data, STEADY), steady=STEADY,
                                      pairs=10)
        out = m.assemble(cells, records, observed)
        self.assertTrue(out["nondeterminism"])
        self.assertEqual(out["status"], "fail")

    def test_markdown_publishes_status_slopes_and_startup_difference(self):
        cells, records, observed = template()
        data = experiment({"startup": 5}, {"startup": 6})
        records[CASE, 0] = dict(an.cell(*data, STEADY), steady=STEADY,
                                pairs=10)
        out = m.assemble(cells, records, observed)
        text = m.results_markdown(out)
        self.assertIn("Status: **pass** (complete: True)", text)
        self.assertIn("| slope pass |", text)
        self.assertIn("| %s | 0 | startup | 5 x10 | 6 x10 | 1 x10 | 0 x10 |"
                      % CASE, text)
        self.assertIn("Unresolved cells: 0", text)


# ------------------------------------------------------------ grid replay

class GridReplay(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.sb = tb.Sandbox(self.tmp.name)
        self.root = Path(self.tmp.name) / "grid"
        self.root.mkdir()
        # run() keeps the controls receipt next to the archives
        shutil.copyfile(self.sb.controls_path,
                        self.root / "controls-receipt.json")

    def inventory(self, rows, **header):
        inventory = dict(self.sb.header(**header), jobs=[1], runs=rows)
        return inventory

    def row(self, case=CASE, size=0, build=None, **kw):
        archive = self.sb.archive(self.tmp.name, build, name=m.name_of(
            case, size), case=case, size=size, where=self.root, **kw)
        return self.sb.inventory_row(archive, case, size)

    def grid(self, build=None):
        inventory = self.inventory([self.row(build=build)])
        a.save(self.root / "inventory.json", inventory)
        decisions = m.finish(self.root, inventory)
        m.write_results(self.root, decisions, not decisions["complete"])
        return inventory

    def test_replay_recomputes_and_matches_written_decisions(self):
        self.grid()
        args = type("Args", (), {"output": self.root})
        self.assertEqual(m.replay(args), 2)  # partial grid: no decision

    def test_replay_detects_changed_decisions_results_and_archive(self):
        self.grid()
        args = type("Args", (), {"output": self.root})
        path = self.root / "decisions-partial.json"
        original = path.read_text()
        changed = json.loads(original)
        changed["status"] = "pass"
        path.write_text(json.dumps(changed))
        with self.assertRaisesRegex(sc.InvalidAllocation, "decisions"):
            m.replay(args)
        path.write_text(original)
        results = self.root / "RESULTS-partial.md"
        results.write_text(results.read_text() + "x\n")
        with self.assertRaisesRegex(sc.InvalidAllocation, "results table"):
            m.replay(args)
        archive = self.root / (m.name_of(CASE, 0) + ".json.xz")
        archive.write_bytes(archive.read_bytes() + b"x")
        with self.assertRaisesRegex(sc.InvalidAllocation, "archive"):
            m.replay(args)

    def test_replay_of_a_failure_reports_it(self):
        build = build_for("candidate", "candidate", 0,
                          work={"apply": {"native": 4}})
        self.grid(build)
        args = type("Args", (), {"output": self.root})
        self.assertEqual(m.replay(args), 1)

    def test_cells_are_bound_to_the_inventory_header(self):
        inventory = self.grid()
        changes = {
            "inputs": {"driver": dict(sha256="e" * 64, bytes=3)},
            "toolchain_products": {"hol": dict(sha256="e" * 64, bytes=1)},
            "tools": {}, "shim": {}, "toolchain_head": "c" * 40,
            "revisions": dict(baseline=BASE, control=BASE, candidate=BASE),
            "canary": {}, "baseline": "c" * 40, "candidate": "c" * 40,
            "environment": dict(inventory["environment"], CC="/x/cc"),
            "boundary": dict(inventory["boundary"], changed=1),
            "harness": dict(inventory["harness"], head="c" * 40),
        }
        for key, value in changes.items():
            with self.subTest(key):
                other = dict(inventory, **{key: value})
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "different inputs"):
                    m.finish(self.root, other)

    def test_a_cell_is_bound_to_the_places_it_was_measured_at(self):
        inventory = self.grid()
        row = inventory["runs"][0]
        self.assertEqual(row["places"], m.places(inventory))
        # Another run's places in the header are no concern of this row ...
        moved = dict(inventory, shim_path="/x/bracket.so",
                     library="/y/libpolyml.so.16.0.0", aliases=[])
        m.finish(self.root, moved)
        # ... but the row must say where it really ran.
        for key, value in (("shim_path", "/x/bracket.so"),
                           ("library", "/y/libpolyml.so.16.0.0"),
                           ("aliases", [])):
            with self.subTest(key):
                other = dict(row, places=dict(row["places"], **{key: value}))
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "different inputs"):
                    m.finish(self.root, dict(inventory, runs=[other]))
        for label, bad in (("absent", None), ("partial", {"library": "x"})):
            with self.subTest(label):
                other = {k: v for k, v in row.items() if k != "places"}
                if bad is not None:
                    other["places"] = bad
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "without the places"):
                    m.finish(self.root, dict(inventory, runs=[other]))

    def moved(self):
        """Another TMPDIR of the length of this sandbox's."""
        return self.sb.tmpdir[:-1] + ("Z" if self.sb.tmpdir[-1] != "Z"
                                      else "Y")

    def test_a_cell_measured_at_a_moved_tmpdir_replays_there(self):
        # The cell ran, and its processes recorded TMPDIR, elsewhere than
        # this session's header says: the row's own places bind it.
        here, there = self.sb.tmpdir, self.moved()
        self.sb.tmpdir = there
        row = self.row()
        self.sb.tmpdir = here
        self.assertEqual(row["places"]["tmpdir"], there)
        inventory = self.inventory([row])
        self.assertEqual(inventory["tmpdir"], here)
        m.finish(self.root, inventory)
        # the row must say where the cell really ran ...
        liar = dict(row, places=dict(row["places"], tmpdir=here))
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "different inputs"):
            m.finish(self.root, dict(inventory, runs=[liar]))
        # ... and a cell run at the header's place, with the header's
        # place for a row, is no different
        self.sb.tmpdir = there
        inventory = self.inventory([row])
        self.assertEqual(inventory["tmpdir"], there)
        m.finish(self.root, inventory)

    def test_cells_of_one_grid_ran_at_paths_of_one_length(self):
        first = self.row(size=0)

        def unresolved(**places):
            """A rejected cell: kept with the places it ran at."""
            return dict(first, size=1, rejected="boom", status="unresolved",
                        places=dict(first["places"], **places))
        place = first["places"]
        m.finish(self.root, self.inventory([
            first, unresolved(tmpdir=self.moved())]))
        for key in ("tmpdir", "library"):
            for text in (place[key] + "x", place[key][:-1]):
                for rows in ([first, unresolved(**{key: text})],
                             [unresolved(**{key: text}), first]):
                    with self.subTest(key=key, text=text):
                        with self.assertRaisesRegex(
                                sc.InvalidAllocation,
                                "paths of different lengths"):
                            m.finish(self.root, self.inventory(rows))
        # places other than these two may differ in length
        m.finish(self.root, self.inventory([first, unresolved(
            shim_path=place["shim_path"] + "x", aliases=[])]))

    def test_the_controls_receipt_is_kept_and_checked_again(self):
        inventory = self.grid()
        copy = self.root / "controls-receipt.json"
        original = copy.read_text()
        # the copy is part of the output, re-verified from its own bytes
        facts = a.load(copy)
        self.assertEqual(a.seal(copy), inventory["controls"]["receipt"])
        copy.write_text(json.dumps(dict(facts, head="c" * 40)))
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "controls receipt copy changed"):
            m.finish(self.root, inventory)
        copy.write_text(original)
        copy.unlink()
        with self.assertRaises((OSError, sc.InvalidAllocation)):
            m.finish(self.root, inventory)
        copy.write_text(original)
        m.finish(self.root, inventory)

    def test_the_controls_copy_must_say_what_the_inventory_says(self):
        inventory = self.grid()
        other_runtime = dict(inventory["runtime"], bytes=99)
        for label, change, message in (
                ("runtime of the grid", dict(runtime=other_runtime),
                 "belongs to another runtime"),
                ("runtime of the entry", dict(controls=dict(
                    inventory["controls"], runtime=other_runtime)),
                 "belongs to another runtime"),
                ("head", dict(controls=dict(
                    inventory["controls"], head="c" * 40)),
                 "facts differ"),
                ("tree", dict(controls=dict(
                    inventory["controls"], tree="e" * 64)),
                 "differs from the candidate"),
                ("libraries", dict(controls=dict(
                    inventory["controls"], libraries={})), "facts differ"),
                ("configuration", dict(controls=dict(
                    inventory["controls"], native_configuration="0")),
                 "facts differ"),
                ("empty entry", dict(controls={}), "malformed"),
                ("no entry", dict(controls=None), "malformed")):
            with self.subTest(label):
                with self.assertRaisesRegex(sc.InvalidAllocation, message):
                    m.finish(self.root, dict(inventory, **change))
        # an entry may not point out of the output
        with self.assertRaises(ValueError):
            m.finish(self.root, dict(inventory, controls=dict(
                inventory["controls"], file="../controls.json")))

    def test_row_is_bound_to_the_archive_case_size_and_steady_count(self):
        inventory = self.grid()
        row = inventory["runs"][0]
        for change in (dict(size=10), dict(case="frag_named")):
            with self.subTest(change):
                other = dict(inventory, runs=[dict(row, **change)])
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "different inputs"):
                    m.finish(self.root, other)
        other = dict(inventory, runs=[dict(row, steady=5)])
        with self.assertRaisesRegex(sc.InvalidAllocation, "steady"):
            m.finish(self.root, other)
        counts = tb.counts(steady=8)
        other = dict(inventory, iterations=counts)
        with self.assertRaisesRegex(sc.InvalidAllocation, "steady"):
            m.finish(self.root, other)

    def test_finish_rejects_duplicate_unknown_and_changed_rows(self):
        inventory = self.grid()
        row = inventory["runs"][0]
        for rows, message in (
                ([row, row], "duplicate"),
                ([dict(row, size=7)], "wrong/duplicate"),
                ([dict(row, case="nothing")], "wrong/duplicate"),
                ([dict(row, seal=dict(row["seal"], bytes=1))],
                 "changed archive"),
                ([dict(row, status="fail")], "changed cell outcome")):
            with self.subTest(rows=message):
                with self.assertRaisesRegex(sc.InvalidAllocation, message):
                    m.finish(self.root, dict(inventory, runs=rows))
        outside = Path(self.tmp.name) / "outside.json.xz"
        outside.write_bytes(b"x")
        with self.assertRaises(ValueError):
            m.finish(self.root, dict(inventory, runs=[dict(
                row, archive="../outside.json.xz")]))

    def test_rejected_row_stays_unresolved(self):
        inventory = self.grid()
        row = dict(inventory["runs"][0], rejected="boom", status="unresolved")
        out = m.finish(self.root, dict(inventory, runs=[row]))
        self.assertEqual(out["unresolved"], [m.name_of(CASE, 0)])

    def test_shared_inputs_must_agree_across_cells(self):
        first = self.row(size=0)
        (self.sb.repo / "src/Heap1.sml").write_text("val heap = 2\n")
        second = self.row(size=1)
        other = self.sb.header()
        inventory = dict(other, jobs=[1], runs=[first, second])
        with self.assertRaisesRegex(sc.InvalidAllocation, "shared input"):
            m.finish(self.root, inventory)


BASE = tb.BASE_PIN


# ------------------------------------------------------------------ inputs

class BoundaryPrefixes(unittest.TestCase):
    PREFIXES = ["src/boss/", "src/real/", "help/Docfiles/"]

    def test_a_path_under_a_prefix_names_it(self):
        repo = Path("/tc/hol")
        for below, prefix in (("src/boss/bossLib.uo", "src/boss/"),
                              ("src/boss/.hol/objs/x.uo", "src/boss/"),
                              ("src/real/a/b.sml", "src/real/"),
                              ("help/Docfiles/HTML/x.htm",
                               "help/Docfiles/")):
            with self.subTest(below):
                self.assertEqual(m.under_prefix(
                    repo, repo / below, self.PREFIXES), prefix)

    def test_other_paths_are_not_under_a_prefix(self):
        repo = Path("/tc/hol")
        for below in ("src/bossy/x.uo", "src/bos", "src/boss", "src/Boss/x",
                      "sigobj/bossLib.uo", "src/marker/markerLib.uo",
                      "bin/hol.state0", "x/src/boss/y", "help/Doc/x"):
            with self.subTest(below):
                self.assertIsNone(m.under_prefix(
                    repo, repo / below, self.PREFIXES))
        self.assertIsNone(m.under_prefix(repo, repo / "src/boss/x", []))

    def test_a_path_outside_the_toolchain_is_refused_not_passed(self):
        repo = Path("/tc/hol")
        for path in ("/src/boss/x", "/tc/hol2/src/boss/x", "/tc/x",
                     "src/boss/x", "/tc"):
            with self.subTest(path):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "outside the toolchain"):
                    m.under_prefix(repo, Path(path), self.PREFIXES)


class TmpdirIsAPlace(unittest.TestCase):
    """TMPDIR (and the path length of the scratch tree below it) is a place
    and not content only while no bracket of the allocation fixture reads an
    environment variable or a path. The one call of the cases that does is
    the `new_theory` of `history_theory_change`: in a `hol run` process it
    exports the theory, which writes *Theory files below the working
    directory and builds words that depend on the clock and the process id.
    MatrixAllocation.sml replaces it by a no-op (MatrixSupport.theoryChange),
    so no allocation bracket reads a path; the timing gate keeps the real
    transition. The case is in the TASK30 allocation gate."""
    CASE_NAME = "history_theory_change"
    SENSITIVE = ("new_theory", "export_theory", "getEnv", "OS.FileSys",
                 "FileSys.", "OS.Process", "Posix.", "TextIO.openIn",
                 "TextIO.openOut", "BinIO.open", "Paired.env", "Portable.pwd")

    @staticmethod
    def code(name):
        return re.sub(r"\(\*.*?\*\)", "", (m.HERE / name).read_text(),
                      flags=re.S)

    def test_the_case_is_gated_while_its_path_use_is_removed(self):
        self.assertNotIn(self.CASE_NAME, gate.CASES)
        self.assertIn(self.CASE_NAME, m.TASKS["task30"].cases)
        self.assertIn("theoryChange := (fn _ => ())",
                      self.code("MatrixAllocation.sml"))

    def test_only_the_default_of_the_hook_has_a_direct_path_token(self):
        # A lexical scan of MatrixSupport.sml alone: it follows no callee.
        text = self.code("MatrixSupport.sml")
        hook = "val theoryChange = ref (fn name => ignore (new_theory name))"
        self.assertEqual(text.count(hook), 1)  # the anchor holds
        text = text.replace(hook, "")
        for token in self.SENSITIVE:
            with self.subTest(token):
                self.assertNotIn(token, text)


class Inputs(unittest.TestCase):
    def counts(self, **kw):
        value = tb.counts(repeats=3)
        value.update(kw)
        return value

    def load(self, value):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "counts.json"
            path.write_text(json.dumps(value))
            return m.load_iterations(path)

    def test_complete_counts_accepted(self):
        self.assertEqual(self.load(self.counts())["repeats"], 3)

    def test_incomplete_or_bad_counts_rejected(self):
        steady = self.counts()["steady"]
        short = dict(steady)
        del short["frag_ac-10000"]
        extra = dict(steady, **{"frag_ac-7": 4})
        for bad in (self.counts(steady=short), self.counts(repeats=2),
                    self.counts(repeats=3.5),
                    self.counts(repeats="3"),
                    self.counts(schema="other"),
                    self.counts(steady=extra),
                    self.counts(steady=dict(steady, **{"frag_ac-10000": 0})),
                    self.counts(steady=dict(steady,
                                            **{"frag_ac-10000": True})),
                    self.counts(steady=dict(steady,
                                            **{"frag_ac-10000": 1.5}))):
            with self.assertRaises(sc.InvalidAllocation):
                self.load(bad)

    def test_committed_counts_cover_the_grid(self):
        counts = m.load_iterations()
        self.assertEqual(len(counts["steady"]), 162)
        self.assertGreaterEqual(counts["repeats"], 3)

    def test_grid_is_27_cases_by_6_sizes(self):
        self.assertEqual((len(gate.CASES), len(m.SIZES), len(m.keys())),
                         (27, 6, 162))

    def test_sides_are_distinct_with_equal_length_names(self):
        self.assertEqual(len(set(m.SIDES.values())), 3)
        self.assertEqual(len({len(v) for v in m.SIDES.values()}), 1)
        self.assertEqual(set(m.SIDES), {"baseline", "control", "candidate"})
        self.assertEqual(m.EXPERIMENTS["control"], ("baseline", "control"))
        self.assertEqual(m.EXPERIMENTS["candidate"],
                         ("baseline", "candidate"))

    def test_binding_digest_depends_on_every_shared_input(self):
        with tempfile.TemporaryDirectory() as tmp:
            sb = tb.Sandbox(tmp)
            base = m.grid_digest(sb.header())
            for key in tb.EXPECTED_GRID_KEYS:
                with self.subTest(key):
                    header = sb.header()
                    header[key] = "changed"
                    self.assertNotEqual(m.grid_digest(header), base)


# ------------------------------------------------- structural evidence (v1)

V1 = sc.STRUCTURE


def counts_text(trace="2.REWRITING=3", kernel="SPEC=2,total=2",
                maker=0, collector=0):
    return "trace=%s;kernel=%s;maker=%d;collector=%d" % (
        trace, kernel, maker, collector)


def v1_events(**kw):
    return process_events(structure=V1, **kw)


def v1_parse(events, **kw):
    return sc.parse(events, case=CASE, size=0, steady=STEADY, repeats=3,
                    structure=kw.pop("structure", V1))


def replace_work(index, text):
    def change(events):
        events[-4 + index][2] = text
    return change


WORK_GUARDS = [
    ("first misnamed", lambda e: e[-4].__setitem__(1, "work.other"),
     "work records"),
    ("second missing", lambda e: e.pop(-3), "observation count"),
    ("digest missing", lambda e: e.pop(-2), "observation count"),
    ("records swapped", lambda e: e.__setitem__(slice(-4, -2),
                                                [e[-3], e[-4]]),
     "work records"),
    ("records before the foreign-thread record", lambda e: e.insert(
        -5, e.pop(-4)), "foreign-thread"),
    ("extra field", lambda e: e[-4].append("x"), "work records"),
    ("unknown section", replace_work(0, "kernel=;trace=;maker=0;"
                                     "collector=0"), "malformed work"),
    ("section missing", replace_work(0, "trace=;kernel="),
     "malformed work"),
    ("unknown trace action", replace_work(0, counts_text("2.NOPE=1")),
     "bad trace key"),
    ("trace level out of range", replace_work(0, counts_text("16.TEXT=1")),
     "bad trace key"),
    ("trace level not a number", replace_work(0, counts_text("x.TEXT=1")),
     "bad trace key"),
    ("trace without a level", replace_work(0, counts_text("TEXT=1")),
     "bad trace key"),
    ("unknown kernel rule", replace_work(0, counts_text(kernel="NOPE=1")),
     "bad kernel key"),
    ("trace keys out of order", replace_work(
        0, counts_text("4.REDUCE=1,2.REWRITING=3")), "out of order"),
    ("kernel keys repeated", replace_work(
        0, counts_text(kernel="SPEC=1,SPEC=1")), "out of order"),
    ("zero count listed", replace_work(0, counts_text("2.TEXT=0")),
     "malformed work count"),
    ("count with a leading zero", replace_work(
        0, counts_text("2.TEXT=01")), "malformed work count"),
    ("negative count", replace_work(0, counts_text("2.TEXT=-1")),
     "malformed work count"),
    ("maker count not a number", replace_work(
        0, counts_text().replace("maker=0", "maker=x")),
     "malformed work count"),
    ("collector with a leading zero", replace_work(
        0, counts_text().replace("collector=0", "collector=00")),
     "malformed work count"),
]


class StructureProtocol(unittest.TestCase):
    def test_a_v1_process_has_its_three_records_after_the_foreign_one(self):
        events = v1_events()
        self.assertEqual([e[1] for e in events[-5:-1]],
                         ["alloc.foreign", *sc.WORK_EVENTS])
        brackets, found = v1_parse(events)
        self.assertEqual([b["name"] for b in brackets], sc.names(3))
        work = sc.work(found, V1)
        self.assertEqual(work["first"], {
            "trace.2.REWRITING": 3, "trace.4.REDUCE": 1,
            "kernel.SPEC": 2, "kernel.total": 2})
        self.assertEqual(work["first"], work["second"])
        self.assertEqual(work, tb.structural())

    def test_the_digest_is_the_sha256_of_the_fingerprint(self):
        import hashlib
        work = tb.structural(digest="a;b")
        self.assertEqual(work["digest"],
                         hashlib.sha256(b"a;b").hexdigest())
        self.assertNotEqual(work["digest"],
                            tb.structural(digest="a;c")["digest"])

    def test_zero_counts_are_absent_and_maker_counts_are_kept(self):
        work = tb.structural(first=counts_text("", "", 3, 1))
        self.assertEqual(work["first"], {"maker": 3, "collector": 1})
        self.assertEqual(tb.structural(first=counts_text("", ""))["first"],
                         {})

    def test_no_header_key_means_no_work_records(self):
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "observation count"):
            v1_parse(v1_events(), structure=None)
        brackets, found = v1_parse(process_events(), structure=None)
        self.assertEqual(len(brackets), len(sc.names(3)))
        self.assertIsNone(sc.work(found, None))

    def test_a_v1_header_demands_them(self):
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "observation count"):
            v1_parse(process_events())

    def test_unknown_versions_are_refused(self):
        for version in ("v2", "", 1, True):
            with self.subTest(version=version), \
                    self.assertRaisesRegex(sc.InvalidAllocation,
                                           "unknown structure"):
                v1_parse(v1_events(), structure=version)

    def test_every_work_guard_is_killed(self):
        for label, change, message in WORK_GUARDS:
            with self.subTest(label):
                events = v1_events()
                change(events)
                with self.assertRaisesRegex(sc.InvalidAllocation, message):
                    v1_parse(events)

    def test_the_word_guards_still_hold_under_v1(self):
        events = v1_events()
        events[-5][2] = "1,0"
        with self.assertRaisesRegex(sc.InvalidAllocation, "foreign-thread"):
            v1_parse(events)

    def test_the_fixture_lists_are_the_schemas(self):
        text = (m.HERE / "MatrixSupport.sml").read_text()
        actions = re.search(r"val traceActions =\s*\[(.*?)\]", text, re.S)
        self.assertEqual(tuple(re.findall(r'"(\w+)"', actions[1])),
                         sc.TRACE_ACTIONS)
        levels = re.search(r"val traceLevels = (\d+)", text)
        self.assertEqual(int(levels[1]), sc.TRACE_LEVELS)
        kernel = re.search(r"fun kernelCounts \(\) =(.*?) end\n", text,
                           re.S)
        self.assertEqual(tuple(re.findall(r'\("(\w+)",#', kernel[1])),
                         sc.KERNEL_RULES)
        order = re.findall(r"Trace\.(\w+) _ => (\d+)", text)
        self.assertEqual([n for n, _ in sorted(order, key=lambda x:
                                               int(x[1]))],
                         list(sc.TRACE_ACTIONS))
        self.assertEqual(sc.WORK_EVENTS, tuple(re.findall(
            r'\("(work\.\w+|result\.digest)",', text)))


def v1_cell(first=None, second=None, digest=None, pairs=10, steady=STEADY,
            **kw):
    """experiment() with structural records; kw reach experiment()."""
    work = tb.structural(**{k: v for k, v in dict(
        first=first, second=second, digest=digest).items()
        if v is not None})
    return experiment({}, {}, pairs=pairs, steady=steady, work=work, **kw)


def with_side(data, side, work, pairs=None, control=False):
    """Replace the work record of one side in the given pairs."""
    lists = data[1] if control else data[0]
    for i in (range(len(lists)) if pairs is None else pairs):
        lists[i][side] = dict(lists[i][side], work=work)
    return data


class StructureDecisions(unittest.TestCase):
    def test_equal_everywhere_is_equal(self):
        cell = an.cell(*v1_cell(), STEADY)
        rows = cell["work"]
        self.assertEqual(set(rows), {
            "digest", "first.trace.2.REWRITING", "first.trace.4.REDUCE",
            "first.kernel.SPEC", "first.kernel.total",
            "second.trace.2.REWRITING", "second.trace.4.REDUCE",
            "second.kernel.SPEC", "second.kernel.total"})
        for name, row in rows.items():
            with self.subTest(name):
                self.assertEqual(row["decision"], "equal")
                self.assertTrue(row["control_identical"])
                self.assertEqual(row["deterministic"],
                                 dict(baseline=True, candidate=True))
                self.assertEqual(row["difference"], {"0": 10})
        self.assertEqual(an.work_status(
            r["decision"] for r in rows.values()), "equal")

    def test_a_cell_without_records_has_no_work_section(self):
        cell = an.cell(*experiment({}, {}), STEADY)
        self.assertNotIn("work", cell)

    def test_one_extra_event_in_one_pair_differs(self):
        data = v1_cell()
        more = tb.structural(first=counts_text("2.REWRITING=4,4.REDUCE=1"))
        with_side(data, "candidate", more, pairs=[3])
        rows = an.cell(*data, STEADY)["work"]
        self.assertEqual(rows["first.trace.2.REWRITING"]["decision"],
                         "differs")
        self.assertEqual(rows["first.trace.2.REWRITING"]["difference"],
                         {"0": 9, "1": 1})
        self.assertEqual(rows["second.trace.2.REWRITING"]["decision"],
                         "equal")
        self.assertFalse(rows["first.trace.2.REWRITING"]["deterministic"]
                         ["candidate"])

    def test_fewer_events_differ_too(self):
        data = v1_cell()
        with_side(data, "candidate", tb.structural(
            first=counts_text("4.REDUCE=1")))
        rows = an.cell(*data, STEADY)["work"]
        self.assertEqual(rows["first.trace.2.REWRITING"]["decision"],
                         "differs")
        self.assertEqual(rows["first.trace.2.REWRITING"]["difference"],
                         {"-3": 10})

    def test_a_key_only_one_side_has_is_a_zero_on_the_other(self):
        data = v1_cell()
        with_side(data, "candidate", tb.structural(
            first=counts_text("2.REWRITING=3,4.REDUCE=1,5.TEXT=2")))
        rows = an.cell(*data, STEADY)["work"]
        row = rows["first.trace.5.TEXT"]
        self.assertEqual((row["decision"], row["baseline"],
                          row["candidate"]), ("differs", {"0": 10},
                                              {"2": 10}))

    def test_maker_and_collector_counts_are_rows(self):
        data = v1_cell(first=counts_text(maker=4, collector=1))
        with_side(data, "candidate", tb.structural(
            first=counts_text(maker=5, collector=1)))
        rows = an.cell(*data, STEADY)["work"]
        self.assertEqual(rows["first.maker"]["decision"], "differs")
        self.assertEqual(rows["first.collector"]["decision"], "equal")

    def test_a_digest_difference_differs(self):
        data = v1_cell()
        with_side(data, "candidate", tb.structural(digest="other"),
                  pairs=[0])
        row = an.cell(*data, STEADY)["work"]["digest"]
        self.assertEqual(row["decision"], "differs")
        self.assertEqual(row["difference"], {"0": 9, "1": 1})
        self.assertEqual(len(row["candidate"]), 2)

    def test_control_divergence_is_inconclusive_not_differs(self):
        data = v1_cell()
        with_side(data, "control", tb.structural(
            first=counts_text("2.REWRITING=9")), pairs=[1], control=True)
        rows = an.cell(*data, STEADY)["work"]
        self.assertEqual(rows["first.trace.2.REWRITING"]["decision"],
                         "inconclusive")
        self.assertFalse(rows["first.trace.2.REWRITING"]
                         ["control_identical"])
        self.assertEqual(an.work_status(
            r["decision"] for r in rows.values()), "inconclusive")

    def test_the_baseline_drifting_in_a_candidate_pair_is_inconclusive(self):
        data = v1_cell()
        with_side(data, "baseline", tb.structural(digest="drift"),
                  pairs=[2])
        row = an.cell(*data, STEADY)["work"]["digest"]
        self.assertEqual(row["decision"], "inconclusive")
        self.assertFalse(row["deterministic"]["baseline"])

    def test_a_nondeterministic_row_is_reported_beside_the_words(self):
        data = v1_cell()
        with_side(data, "candidate", tb.structural(
            first=counts_text("2.REWRITING=4,4.REDUCE=1")), pairs=[0])
        record = dict(an.cell(*data, STEADY), steady=STEADY, pairs=10)
        out = m.assemble({(CASE, 0)}, {(CASE, 0): record},
                         {(CASE, 0): data})
        self.assertIn([CASE, 0, "first.trace.2.REWRITING", "candidate"],
                      out["work"]["nondeterminism"])
        self.assertNotIn([CASE, 0, "first.trace.2.REWRITING", "baseline"],
                         out["work"]["nondeterminism"])
        # the words' own list is untouched
        self.assertEqual(out["nondeterminism"], [])

    def test_work_never_enters_slopes_constants_or_the_words_status(self):
        cells, records, observed = template()
        for size in a.SIZES:
            data = experiment({"setup": 10}, {"setup": 10}, work=(
                tb.structural(), tb.structural(digest="other")))
            records[CASE, size] = dict(an.cell(*data, STEADY),
                                       steady=STEADY, pairs=10)
            observed[CASE, size] = data
        plain = m.assemble(*template())
        out = m.assemble(cells, records, observed)
        self.assertEqual(out["status"], plain["status"])
        self.assertEqual(out["work_status"], "differs")
        self.assertEqual(out["work"]["status"], "differs")
        self.assertEqual(out["nondeterminism"], plain["nondeterminism"])
        record = out["cases"][CASE]
        self.assertEqual(record["slopes"],
                         plain["cases"][CASE]["slopes"])
        self.assertEqual(record["constants"],
                         plain["cases"][CASE]["constants"])
        self.assertEqual(an.case_decisions(record),
                         an.case_decisions(plain["cases"][CASE]))
        self.assertEqual(set(record["slopes"]), set(an.GATED))

    def test_a_failing_word_row_does_not_make_the_work_differ(self):
        data = experiment({"setup": 10}, {"setup": 11}, work=tb.structural())
        record = dict(an.cell(*data, STEADY), steady=STEADY, pairs=10)
        out = m.assemble({(CASE, 0)}, {(CASE, 0): record},
                         {(CASE, 0): data})
        self.assertEqual(out["status"], "fail")
        self.assertEqual(out["work_status"], "equal")

    def test_a_mixed_cell_is_refused(self):
        data = v1_cell()
        data[0][0]["candidate"] = observation({})
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "some processes"):
            an.cell(*data, STEADY)

    def test_the_markdown_has_a_structural_section_only_with_work(self):
        cells, records, observed = template()
        plain = m.results_markdown(m.assemble(cells, records, observed))
        self.assertNotIn("Structural", plain)
        data = v1_cell()
        records[CASE, 0] = dict(an.cell(*data, STEADY), steady=STEADY,
                                pairs=10)
        out = m.assemble(cells, records, observed)
        text = m.results_markdown(out)
        self.assertIn("Structural evidence", text)
        self.assertIn("**equal**", text)
        self.assertIn("| %s | 0 | equal |" % CASE, text)
        self.assertIn("Status: **pass**", text)


class StructureReplay(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.sb = tb.Sandbox(self.tmp.name)

    def replay(self, build=None, header=None, **kw):
        out = self.sb.archive(self.tmp.name, build, **kw)
        bind = self.sb.bind(**(header if header is not None else kw))
        return m.replay_cell(out, bind)

    def test_a_v1_archive_replays_with_its_work_rows(self):
        result = self.replay(structure=V1)
        record = result["record"]
        self.assertEqual(m.cell_status(record), "pass")
        self.assertEqual({r["decision"] for r in record["work"].values()},
                         {"equal"})
        self.assertEqual(result["observed"][0][0]["candidate"]["work"],
                         tb.structural())

    def test_an_archive_without_the_key_replays_as_before(self):
        record = self.replay()["record"]
        self.assertNotIn("work", record)
        cells, records, observed = {(CASE, 0)}, {(CASE, 0): record}, {}
        out = m.assemble(cells, records, observed)
        self.assertNotIn("work", out)
        self.assertNotIn("work_status", out)
        self.assertNotIn("Structural", m.results_markdown(out))

    def test_the_digest_and_meta_of_an_old_header_are_unchanged(self):
        import hashlib
        header = self.sb.header()
        self.assertNotIn("structure", header)
        shared = {k: header[k] for k in m.GRID_KEYS}
        legacy = hashlib.sha256(json.dumps(
            shared, sort_keys=True, allow_nan=False).encode()).hexdigest()
        self.assertEqual(m.grid_digest(header), legacy)
        self.assertNotIn("structure", self.sb.bind())
        v1 = self.sb.header(structure=V1)
        self.assertNotEqual(m.grid_digest(v1), legacy)
        self.assertEqual(self.sb.bind(structure=V1)["structure"], V1)

    def test_records_under_a_header_without_the_key_are_refused(self):
        def build(experiment, side, pair):
            return dict(structure=V1)
        out = self.sb.archive(self.tmp.name, build)
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "observation count"):
            m.replay_cell(out, self.sb.bind())

    def test_a_missing_record_under_a_v1_header_is_refused(self):
        def build(experiment, side, pair):
            return dict(structure=None)
        out = self.sb.archive(self.tmp.name, build, structure=V1)
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "observation count"):
            m.replay_cell(out, self.sb.bind(structure=V1))

    def test_a_cell_is_bound_to_the_structure_of_its_header(self):
        out = self.sb.archive(self.tmp.name, structure=V1)
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "different inputs"):
            m.replay_cell(out, self.sb.bind())
        out = self.sb.archive(self.tmp.name, name="plain")
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "different inputs"):
            m.replay_cell(out, self.sb.bind(structure=V1))

    def test_a_digest_difference_in_one_process_is_detected(self):
        build = build_for("candidate", "candidate", 3, structure=V1,
                          records=tb.structural_events(digest="other"))
        record = self.replay(build, structure=V1)["record"]
        row = record["work"]["digest"]
        self.assertEqual(row["decision"], "differs")
        self.assertEqual(m.cell_status(record), "pass")

    def test_a_nondeterministic_count_is_detected_and_the_words_pass(self):
        build = build_for("candidate", "candidate", 3, structure=V1,
                          records=tb.structural_events(
                              first=counts_text("2.REWRITING=4")))
        record = self.replay(build, structure=V1)["record"]
        row = record["work"]["first.trace.2.REWRITING"]
        self.assertFalse(row["deterministic"]["candidate"])
        self.assertEqual(row["decision"], "differs")
        self.assertEqual(m.cell_status(record), "pass")

    def test_the_header_of_a_new_run_says_v1(self):
        sb = self.sb
        grid = sb.real_grid()
        with grid.make():
            header = dict(grid.make_header(
                tb.CAND_PIN, sb.header()["toolchain_products"]),
                iterations=tb.counts())
        self.assertEqual(header["structure"], V1)
        old = dict(header)
        del old["structure"]
        self.assertIn("structure", m.changed_settings(old, header))
        self.assertEqual(m.changed_settings(header, header), [])
        self.assertNotEqual(m.grid_digest(header), m.grid_digest(old))

    def test_finish_and_replay_write_the_work_section(self):
        root = Path(self.tmp.name) / "grid"
        root.mkdir()
        shutil.copyfile(self.sb.controls_path, root / "controls-receipt.json")
        archive = self.sb.archive(self.tmp.name, name=m.name_of(CASE, 0),
                                  where=root, structure=V1)
        record = m.replay_cell(archive, self.sb.bind(structure=V1))["record"]
        row = dict(case=CASE, size=0, steady=STEADY, rejected=None,
                   archive=archive.name, seal=tb.seal(archive), files=0,
                   places=m.places(self.sb.header(structure=V1)),
                   status=m.cell_status(record))
        inventory = dict(self.sb.header(structure=V1), jobs=[1], runs=[row])
        a.save(root / "inventory.json", inventory)
        decisions = m.finish(root, inventory)
        self.assertEqual(decisions["work_status"], "equal")
        self.assertEqual(decisions["work"]["cells"], {m.name_of(CASE, 0):
                                                      "equal"})
        m.write_results(root, decisions, not decisions["complete"])
        args = type("Args", (), {"output": root})
        self.assertEqual(m.replay(args), 2)  # a partial grid decides nothing
        self.assertIn("Structural evidence",
                      (root / "RESULTS-partial.md").read_text())


if __name__ == "__main__":
    unittest.main()
