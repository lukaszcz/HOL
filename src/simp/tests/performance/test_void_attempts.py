#!/usr/bin/env python3
"""The environment-integrity rule of void_attempts.py (TASK37 decision 45),
against real engines, ledgers and archives: a runner that refused after
admitting pairs because its environment changed is void only when the
caller names the refusals, and every other archive is judged as before."""
import re
import unittest

import acceptance as a
import void_attempts as va
from test_task31_attempts import World, follow, tg

REFUSAL = "runtime/tool changed during pair"
ADMITTED = [dict(receipt="pair-01-a.json.gz", accepted=True,
                 expected_acceptance=True, exit=0)]


class Source(unittest.TestCase):
    def test_the_refusal_texts_are_those_of_the_runner(self):
        text = (a.HERE.parent / "compatibility" /
                "run_paired.py").read_text()
        self.assertEqual(len(va.ENVIRONMENT_REFUSALS), 5)
        for refusal in va.ENVIRONMENT_REFUSALS:
            self.assertEqual(len(re.findall(
                r'"%s"' % re.escape(refusal), text)), 1, refusal)
        # every require() of the runner's integrity checks is named
        for found in re.findall(
                r'"((?:[a-z/ ]+) changed during (?:pair|experiment))"',
                text):
            self.assertIn(found, va.ENVIRONMENT_REFUSALS)
        self.assertIsInstance(va.ENVIRONMENT_REFUSALS, frozenset)


class Environment(World):
    def setUp(self):
        super().setUp()
        self.engine = self.follow

    def cell(self, name, *manifests, success=False, timed_out=False):
        """A packed archive of a failed acceptance whose commands each
        left a runner manifest (`manifests`: dicts, one per command)."""
        folder = self.root / ("src-" + name)
        folder.mkdir()
        commands = []
        for i, manifest in enumerate(manifests):
            commands.append(dict(argv=["run", "--output", "out%d" % i],
                                 timed_out=timed_out))
            (folder / ("out%d" % i)).mkdir()
            a.save(folder / ("out%d" % i) / "manifest.json", manifest)
        a.save(folder / "acceptance.json",
               dict(success=success, commands=commands))
        archive = self.root / (name + ".json.xz")
        tg.bundle.pack(folder, archive)
        return archive

    def attempt(self, name, archive):
        """A void-shaped attempt whose every cell holds `archive`."""
        self.archive = archive
        out = self.output(self.engine, name, "V")
        self.lines(self.engine, "V", "first", out, "open", "close",
                   status="inconclusive")
        judged = self.output(self.engine, name + "-j", "J")
        self.lines(self.engine, "J", "first", judged, "open", "close",
                   status="pass")
        return judged

    def refused(self, **more):
        return dict(runs=ADMITTED, success=False, failure=REFUSAL, **more)

    def run_attempts(self, judged, refusals=frozenset()):
        return va.attempts_of(self.args, self.engine, {"J": judged},
                              refusals)

    def test_an_environment_refusal_is_void_only_with_the_set(self):
        judged = self.attempt("env", self.cell("env", self.refused()))
        with self.assertRaisesRegex(ValueError, "admitted run"):
            self.run_attempts(judged)
        found = self.run_attempts(judged, va.ENVIRONMENT_REFUSALS)
        self.assertEqual([(f["attempt"], f["void"]) for f in found],
                         [("V", True), ("J", False)])
        self.assertEqual(found[0]["environment"], [REFUSAL])
        self.assertNotIn("environment", found[1])

    def test_other_manifests_may_be_unrun_or_succeeded(self):
        unrun = dict(runs=[], success=False, failure="harness died")
        done = dict(runs=ADMITTED, success=True)
        # `out0`, `out1` ...: the order the archive is read in is sorted,
        # so the refusal is first in one case and last in the other
        for label, others, first in (
                ("unrun", (unrun,), False), ("done", (done,), False),
                ("refusal first, unrun after", (unrun,), True),
                ("refusal first, done after", (done,), True)):
            with self.subTest(label):
                manifests = (self.refused(),) + others if first else \
                    others + (self.refused(),)
                name = "case%d" % len(list(self.root.glob("case*.xz")))
                judged = self.attempt(name, self.cell(name, *manifests))
                found = self.run_attempts(judged, va.ENVIRONMENT_REFUSALS)
                self.assertTrue(found[0]["void"])
                self.assertEqual(found[0]["environment"], [REFUSAL])
                self.ledger.unlink()  # the next case: a fresh ledger

    def test_a_failure_that_is_not_an_environment_refusal_stays_judged(
            self):
        other = dict(runs=ADMITTED, success=False, failure="a test failed")
        judged = self.attempt("other", self.cell("other", other))
        with self.assertRaisesRegex(ValueError, "admitted run"):
            self.run_attempts(judged, va.ENVIRONMENT_REFUSALS)

    def test_a_failure_that_is_no_string_stays_judged(self):
        odd = dict(runs=ADMITTED, success=False, failure=[REFUSAL])
        judged = self.attempt("odd", self.cell("odd", odd))
        with self.assertRaisesRegex(ValueError, "admitted run"):
            self.run_attempts(judged, va.ENVIRONMENT_REFUSALS)

    def test_admitted_runs_without_a_failure_stay_judged(self):
        silent = dict(runs=ADMITTED, success=False)
        judged = self.attempt("silent", self.cell(
            "silent", silent, self.refused()))
        with self.assertRaisesRegex(ValueError, "admitted run"):
            self.run_attempts(judged, va.ENVIRONMENT_REFUSALS)

    def test_a_refusal_beside_a_failed_manifest_with_runs_is_judged(self):
        bad = dict(runs=ADMITTED, success=False, failure="a test failed")
        judged = self.attempt("mixed", self.cell(
            "mixed", bad, self.refused()))
        with self.assertRaisesRegex(ValueError, "admitted run"):
            self.run_attempts(judged, va.ENVIRONMENT_REFUSALS)

    def test_the_other_conditions_still_hold_with_the_set(self):
        for name, more, message in (
                ("timed", dict(timed_out=True), "timed out"),
                ("won", dict(success=True), "did not fail")):
            with self.subTest(name):
                judged = self.attempt(name, self.cell(
                    name, self.refused(), **more))
                with self.assertRaisesRegex(ValueError, message):
                    self.run_attempts(judged, va.ENVIRONMENT_REFUSALS)
                self.ledger.unlink()

    def test_the_default_is_the_rule_without_refusals(self):
        unrun = dict(runs=[], success=False, failure="harness died")
        judged = self.attempt("plain", self.cell("plain", unrun))
        found = self.run_attempts(judged)
        self.assertEqual(found, self.run_attempts(judged, frozenset()))
        self.assertTrue(found[0]["void"])
        self.assertEqual(set(found[0]), {
            "attempt", "status", "output", "judged", "void"})
        self.run_attempts(judged, va.ENVIRONMENT_REFUSALS)
        # an unrun-only archive is not an environment void
        self.assertNotIn("environment", self.run_attempts(
            judged, va.ENVIRONMENT_REFUSALS)[0])


if __name__ == "__main__":
    unittest.main()
