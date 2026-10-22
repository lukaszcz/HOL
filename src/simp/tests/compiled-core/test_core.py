#!/usr/bin/env python3
"""Validator mutation tests; no HOL processes or measured batches."""
import copy
from pathlib import Path
import sys
import unittest

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import schema
import run_core


def protocol(events):
    return "".join("@@PAIR\t" + str(i) + "\t" + "\t".join(e) + "\n"
                   for i, e in enumerate(events))


def graph_events():
    events = []
    for n in schema.SIZES:
        events.append(["check", "proofs " + str(n), "pass"])
        for label in schema.LABELS:
            words = 5 * n if label == "cells" else 7 + 3 * n
            events.extend([["observation", "graph." + label,
                            f"{n},10,{10 + words},{words}"],
                           ["check", label + " " + str(n), "pass"]])
    return events + [["observation", "complete",
                      "TASK16-compiled-core-graph-v1"]]


class CoreTests(unittest.TestCase):
    def rejects(self, events):
        with self.assertRaises(ValueError):
            schema.graph(protocol(events))

    def test_graph(self):
        events = graph_events()
        obs, rows = schema.graph(protocol(events))
        self.assertEqual(events, obs)
        self.assertEqual(rows["compiled"][-1]["rules"], 10000)
        selections = {side: {"graphs": rows}
                      for side in ("baseline", "candidate")}
        result = schema.comparison(selections)
        self.assertEqual(result["compiled"]["candidate_minus_baseline_words"],
                         [0] * 6)
        self.assertEqual(result["compiled"]["adjacent_words_per_rule"]
                         ["candidate"], [3.] * 5)

    def test_graph_mutations(self):
        original = graph_events()
        for index in range(len(original)):
            self.rejects(original[:index] + original[index + 1:])
        for value in ("0,10,18,7", "0,10,17,7.0", "1,10,17,7",
                      "0,10,17,~7", "0,10,17,nan", "0,10,17,7,0"):
            events = copy.deepcopy(original)
            events[1][2] = value
            self.rejects(events)
        events = copy.deepcopy(original)
        events[9][2] = "0,10,11,1"
        self.rejects(events)  # sensitivity, not merely subtraction
        self.rejects(original + [original[-1]])
        events = copy.deepcopy(original)
        events[1], events[3] = events[3], events[1]
        self.rejects(events)
        events = copy.deepcopy(original)
        events[2][2] = "fail"
        self.rejects(events)

    def test_protocol_truncation(self):
        with self.assertRaises(ValueError):
            schema.graph(protocol(graph_events())[:-1])

    def test_core_complete_and_ordered(self):
        events = [["check", name, "pass"] for name in schema.CHECKS]
        events[12:12] = [["observation", f"pp.simpset.{width}", "set\\nbody"]
                         for width in (40, 80)]
        events.append(["observation", "complete",
                       "TASK16-compiled-core-behavior-v1"])
        self.assertEqual(schema.behavior(protocol(events)), events)
        for index in range(len(events)):
            with self.assertRaises(ValueError):
                schema.behavior(protocol(events[:index] + events[index + 1:]))
        candidate = copy.deepcopy(events)
        candidate[12][2] += " "
        schema.behavior(protocol(candidate))  # shape alone is insufficient
        with self.assertRaises(ValueError):
            schema.routes.same_behavior(events, candidate)

    def test_no_short_timing_campaign(self):
        args = run_core.options(["--output", "/unused"])
        self.assertEqual(args.performance_pairs, 0)
        self.assertEqual(run_core.options(["--output", "/unused",
            "--performance-pairs", "10"]).performance_pairs, 10)


if __name__ == "__main__":
    unittest.main()
