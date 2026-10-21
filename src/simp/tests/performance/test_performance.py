#!/usr/bin/env python3
"""Fail-closed performance schema controls (no benchmark workload)."""
import copy
import unittest

from performance_schema import CONSUMED, LABELS, validate


class PerformanceTests(unittest.TestCase):
    def setUp(self):
        # wall,nongc usr/sys,GC usr/sys,inclusive CPU usr/sys,GC user,sink
        self.times = "0.25,0.20,0.01,0.02,0.005,0.22,0.015,0.02,10"
        accounting = self.times.rsplit(",", 1)[0] + ",5"
        self.events = [["observation", "timer.accounting", accounting],
                       ["check", "timer accounting", "pass"],
                       ["check", "workload inputs", "pass"]]
        for n in (0, 10, 100, 1000):
            self.events += [["observation", "storage",
                             f"{n},100,200,300,250,350,100,101,150,200,50"],
                            ["check", "retained graphs", "pass"]]
        for label in LABELS:
            ts = self.times.rsplit(",", 1)[0] + "," + str(CONSUMED[label])
            self.events.append(["observation", "calibration." + label,
                                "1," + ts])
            for i in range(3):
                self.events += [["observation", "batch." + label, f"{i},1," + ts],
                                ["check", "results " + label, "pass"]]
        total = 5 + 4 * sum(CONSUMED.values())
        self.events.append(["observation", "sink", str(total)])

    def test_complete(self):
        es, data = validate(self.events, 3, 0.2)
        self.assertEqual(es, self.events)
        self.assertEqual(len(data["workloads"]), 11)
        self.assertEqual(len(data["storage"]), 4)

    def test_every_event_required(self):
        for i in range(len(self.events)):
            with self.subTest(i=i), self.assertRaises(ValueError):
                validate(self.events[:i] + self.events[i + 1:], 3, 0.2)

    def test_duplicates_and_exceptions(self):
        for e in (self.events[-1], ["exception", "Fail", "bad result"]):
            with self.assertRaises(ValueError):
                validate(self.events + [e], 3, 0.2)

    def test_corrupt_timing(self):
        index = next(i for i, e in enumerate(self.events)
                     if e[1].startswith("batch."))
        for field, value in ((2, "NaN"), (2, "~1.0"), (3, "inf"),
                             (7, "100"), (10, "0"), (0, "1"), (1, "2")):
            with self.subTest(field=field, value=value):
                es = copy.deepcopy(self.events)
                fields = es[index][-1].split(",")
                fields[field] = value
                es[index][-1] = ",".join(fields)
                with self.assertRaises(ValueError):
                    validate(es, 3, 0.2)

    def test_short_batch(self):
        es = copy.deepcopy(self.events)
        for e in es:
            if e[1].startswith("batch."):
                e[-1] = e[-1].replace("0.25", "0.01")
                break
        with self.assertRaisesRegex(ValueError, "too short"):
            validate(es, 3, 0.2)

    def test_calibration_required_and_doubling(self):
        es = copy.deepcopy(self.events)
        i = next(i for i, e in enumerate(es)
                 if e[1].startswith("calibration."))
        ts = self.times.rsplit(",", 1)[0] + ",1000"
        es[i][-1] = "2," + ts
        with self.assertRaisesRegex(ValueError, "non-doubling"):
            validate(es, 3, 0.2)
        es[i][-1] = "1," + ts.replace("0.25", "0.1")
        with self.assertRaisesRegex(ValueError, "ordered performance"):
            validate(es, 3, 0.2)

    def test_storage_subtraction(self):
        es = copy.deepcopy(self.events)
        es[3][-1] = "0,100,200,300,250,350,99,101,150,200,50"
        with self.assertRaisesRegex(ValueError, "storage subtraction"):
            validate(es, 3, 0.2)

    def test_gc_control(self):
        es = copy.deepcopy(self.events)
        es[0][-1] = "0.25,0.2,0.01,0,0,0.2,0.01,0,10"
        with self.assertRaisesRegex(ValueError, "did not exercise GC"):
            validate(es, 3, 0.2)


if __name__ == "__main__":
    unittest.main()
