#!/usr/bin/env python3
"""Harness-only parser/validator controls, without rebuilding HOL."""
import copy
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest

import run_paired as runner


class ProtocolTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="paired-validator-")
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.private = self.repo / "baseline"
        self.private.mkdir()
        (self.repo / "sigobj").mkdir()
        for name in ("Paired", "Traverse", "simpLib", "selftest"):
            (self.private / (name + ".sml")).write_text("(* fixture *)\n")
        self.args = dict(selection="baseline", fixture="selftest", control="none",
                         private=self.private, repo=self.repo,
                         private_names={"Traverse", "simpLib"}, flavor="baseline",
                         signature="pass", source_hashes={})
        self.events = [
            ["begin", "baseline", "selftest", "none"],
            ["cwd", str(self.private)],
            ["holdir", str(self.repo), str(self.repo)],
            ["preloaded", "HolKernel,Paired"],
            ["heapfile", str(self.private / "Paired.sml")],
            ["search", str(self.private)],
            ["search", str(self.repo / "sigobj")],
        ]
        for name in ("Traverse", "simpLib", "selftest"):
            self.events.append(["use", str(self.private / (name + ".sml"))])
            if name == "selftest":
                self.events.extend(runner.behavior_events("baseline"))
            self.events.append(["used", str(self.private / (name + ".sml"))])
        self.events.extend(["loaded", str(self.private / (name + ".sml"))]
                           for name in ("Paired", "Traverse", "simpLib", "selftest"))
        self.events.append(["end", "pass", "3"])

    def receipt(self, events=None):
        events = self.events if events is None else events
        text = "".join(runner.PREFIX + str(i) + "\t" + "\t".join(e) + "\n"
                       for i, e in enumerate(events))
        return dict(stdout=text, exit=0, timed_out=False)

    def reject(self, events, reason):
        with self.assertRaisesRegex(runner.InvalidRun, reason):
            runner.validate(self.receipt(events), **self.args)

    def test_complete(self):
        result = runner.validate(self.receipt(), **self.args)
        self.assertEqual(result["outcome"], "pass")
        self.assertEqual(result["expected_test_count"], 3)

    def test_observation_contract(self):
        for kind in ("missing", "duplicate", "wrong", "unordered"):
            with self.subTest(kind=kind):
                es = copy.deepcopy(self.events)
                i = next(i for i, e in enumerate(es) if e[0] == "observation")
                if kind == "missing":
                    del es[i]
                elif kind == "duplicate":
                    es.insert(i, es[i])
                elif kind == "wrong":
                    es[i][-1] = "wrong"
                else:
                    es[i], es[i + 1] = es[i + 1], es[i]
                self.reject(es, "ordered observations")

    def test_inventories_are_complete(self):
        es = [e for e in self.events if e !=
              ["loaded", str(self.private / "Traverse.sml")]]
        self.reject(es, "incomplete or untraced loaded-source inventory")
        es = copy.deepcopy(self.events)
        es[3][-1] += ",Traverse"
        self.reject(es, "already present")

    def test_wrong_path_with_identical_contents(self):
        other = self.repo / "candidate"
        other.mkdir()
        (other / "Traverse.sml").write_bytes(
            (self.private / "Traverse.sml").read_bytes())
        es = [[str(other / "Traverse.sml") if f ==
               str(self.private / "Traverse.sml") else f for f in e]
              for e in self.events]
        self.reject(es, "wrong loaded simplifier path")

    def test_source_mutation(self):
        path = self.private / "Traverse.sml"
        self.args["source_hashes"][str(path)] = runner.fingerprint(path)
        path.write_text("(* changed *)\n")
        self.reject(self.events, "source changed during run")

    def test_failed_process(self):
        r = self.receipt()
        r["exit"] = 7
        with self.assertRaisesRegex(runner.InvalidRun, "failed process"):
            runner.validate(r, **self.args)

    def test_timeout(self):
        r = self.receipt()
        r["timed_out"] = True
        with self.assertRaisesRegex(runner.InvalidRun, "timed out"):
            runner.validate(r, **self.args)

    def test_no_launcher_or_footer(self):
        self.reject([], "launcher not executed")
        self.reject(self.events[:-1], "completion/test count")
        es = copy.deepcopy(self.events)
        es[-1][-1] = "2"
        self.reject(es, "completion/test count")

    def test_transport_corruption(self):
        text = self.receipt()["stdout"]
        for broken in (text[:-1], text.replace("@@PAIR\t5\tsearch", "bad"),
                       text.replace("@@PAIR\t5\t", "@@PAIR\t6\t")):
            with self.subTest(broken=broken[-40:]):
                with self.assertRaises(runner.InvalidRun):
                    runner.parse_events(broken)

    def test_unexpected_event(self):
        es = copy.deepcopy(self.events)
        es.insert(7, ["unknown", "value"])
        self.reject(es, "unknown protocol event")

    def test_expected_red_is_not_a_pass(self):
        es = copy.deepcopy(self.events)
        old = iter(runner.behavior_events("reviewed"))
        es = [next(old) if e[0] in ("observation", "check") else e for e in es]
        args = dict(self.args, flavor="reviewed")
        self.assertEqual(runner.validate(self.receipt(es), **args)["outcome"],
                         "expected-candidate-red")

    def test_arbitrary_static_error_not_signature_rejection(self):
        # Even an exception/footer/exit shaped like expected-red cannot stand
        # in for the original signature's two constructor diagnostics.
        path = self.private / "SignatureCheck.sml"
        path.write_text("(* signature control *)\n")
        es = copy.deepcopy(self.events[:7])
        es[0][2] = "signature"
        es += [["use", str(path)],
               ["exception", "Fail", r'Fail \"Static Errors\"'],
               ["loaded", str(self.private / "Paired.sml")],
               ["end", "error", "0"]]
        r = self.receipt(es)
        r["exit"] = 1
        args = dict(self.args, fixture="signature", signature="reject")
        with self.assertRaisesRegex(runner.InvalidRun, "exact datatype rejection"):
            runner.validate(r, **args)

    def test_timeout_kills_child(self):
        marker = self.repo / "leaked-child"
        child = "import time,pathlib; time.sleep(1); pathlib.Path(" + \
                repr(str(marker)) + ").touch()"
        parent = "import subprocess,time; subprocess.Popen([" + \
                 repr(sys.executable) + ", '-c', " + repr(child) + "]); time.sleep(5)"
        r = runner.execute([sys.executable, "-c", parent], self.repo,
                           os.environ.copy(), 0.2)
        self.assertTrue(r["timed_out"])
        time.sleep(1.1)
        self.assertFalse(marker.exists(), "child escaped timeout cleanup")


if __name__ == "__main__":
    unittest.main()
