#!/usr/bin/env python3
"""Fail-closed parser/comparison controls; no HOL or timing execution."""
import copy
import unittest

import task12_allocation as probe
from run_paired import InvalidRun


def protocol():
    events = []
    for kind in probe.KINDS + ["cells"]:
        for n in probe.SIZES:
            key = "control.cells" if kind == "cells" else "graph." + kind
            row = [n, 5 * n] if kind == "cells" else [n, 23*n, 13*n, 14*n, 3*n]
            events += [["observation", key, ",".join(map(str, row))],
                       ["check", kind + " " + str(n), "pass"]]
    return "".join("@@PAIR\t" + str(i) + "\t" + "\t".join(e) + "\n"
                   for i, e in enumerate(events))


def listing():
    suffixes = ["(3)(1)(1)(1)solver'(1)", "(3)(1)(1)(1)", "(3)(1)(1)",
                "(3)(1)", "(3)", "(1)(1)", "(1)"]
    return "".join("Cond_rewr.COND_REWR_CONV" + s + ":\n" +
                   "000000  F9401B50        ldr     x16,[x26,#48]\n" +
                   "000004  D1006369        sub     x9,x27,#24\n"
                   for s in suffixes)


def selections():
    _, graphs = probe.measurements(protocol())
    selected = dict(graphs=graphs, assembly=probe.assembly(listing()))
    return {s: copy.deepcopy(selected) for s in ("baseline", "candidate")}


class AllocationControls(unittest.TestCase):
    def test_measurements(self):
        observations, graphs = probe.measurements(protocol())
        self.assertEqual(len(observations), 48)
        self.assertEqual(graphs["ac"]["adjacent_words_per_rule"],
                         [[23, 13, 14, 3]] * 5)

    def test_missing_measurement(self):
        with self.assertRaises(InvalidRun):
            probe.measurements(protocol().replace("graph.ac", "graph.other"))

    def test_wrong_arity(self):
        with self.assertRaises(InvalidRun):
            probe.measurements(protocol().replace("0,0,0,0,0", "0,0,0,0"))

    def test_truncated(self):
        with self.assertRaises(InvalidRun):
            probe.measurements(protocol()[:-1])

    def test_sequence(self):
        with self.assertRaises(InvalidRun):
            probe.measurements(protocol().replace("@@PAIR\t1\t", "@@PAIR\t2\t"))

    def test_missing_assembly(self):
        with self.assertRaises(InvalidRun):
            probe.assembly("")

    def test_wrong_architecture(self):
        with self.assertRaises(InvalidRun):
            probe.assembly(listing().replace("ldr     ", "mov     "))

    def test_equal_control(self):
        result = probe.compare(selections())
        self.assertTrue(result["no_extra_retained_words_per_rule"])
        self.assertTrue(result["byte_identical_machine_code"])

    def test_increased_graph(self):
        selected = selections()
        for row in selected["candidate"]["graphs"]["ac"][
                "adjacent_words_per_rule"]:
            row[0] += 1
        with self.assertRaisesRegex(InvalidRun, "increased per-rule graph"):
            probe.compare(selected)

    def test_nonlinear_graph(self):
        selected = selections()
        selected["candidate"]["graphs"]["ac"][
            "adjacent_words_per_rule"][0][0] -= 1
        with self.assertRaisesRegex(InvalidRun, "nonlinear graph slope"):
            probe.compare(selected)

    def test_cell_sensitivity(self):
        selected = selections()
        selected["candidate"]["graphs"]["cells"]["rows"][-1][1] -= 1
        with self.assertRaisesRegex(InvalidRun, "positive allocation control"):
            probe.compare(selected)

    def test_new_reservation(self):
        selected = selections()
        app = "Cond_rewr.COND_REWR_CONV(3)(1)(1)(1)"
        selected["candidate"]["assembly"][app]["reservation_sites"].append(
            dict(offset="000008", bytes=16))
        with self.assertRaisesRegex(InvalidRun, "generated allocation site"):
            probe.compare(selected)

    def test_new_call(self):
        selected = selections()
        app = "Cond_rewr.COND_REWR_CONV(3)(1)(1)(1)"
        selected["candidate"]["assembly"][app]["indirect_calls"] += 1
        with self.assertRaisesRegex(InvalidRun, "call count differs"):
            probe.compare(selected)


if __name__ == "__main__":
    unittest.main()
