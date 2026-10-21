"""Staged shape, semantic expectations and fail-closed regression controls."""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import run_paired as runner
import staging_contracts as staging
import test_runner


def observations(flavor="baseline"):
    return staging.expectation(runner.HERE, flavor)["observations"]


class StagingTests(unittest.TestCase):
    def test_complete_stages_and_actual_validation_counts(self):
        self.assertEqual(staging.shape(observations()), 57)
        self.assertEqual(staging.shape(observations("reviewed")), 54)
        self.assertEqual(len(staging.SCENARIOS), 43)

    def test_missing_reconstruction_is_not_a_pass(self):
        es = observations()
        es = [e for e in es if e[1] != "req0.first.proof.prims"]
        with self.assertRaisesRegex(ValueError, "missing/unordered stage"):
            staging.shape(es)

    def test_count_cannot_replace_execution(self):
        es = observations()
        es[-1][2] = "58"
        with self.assertRaisesRegex(ValueError, "not executed"):
            staging.shape(es)

    def test_extra_oracle_rejected(self):
        es = observations()
        next(e for e in es if e[1] == "req0.first.oracles")[2] = "ValidityCheck"
        with self.assertRaisesRegex(ValueError, "oracle in reconstructed"):
            staging.shape(es)

    def test_reference_seal_rejects_changed_fixture(self):
        with tempfile.TemporaryDirectory(prefix="staging-seal-") as tmp:
            here = Path(tmp)
            shutil.copytree(runner.HERE / "staging", here / "staging")
            with (here / "staging/Staging.sml").open("a") as out:
                out.write("(* accommodate delayed wrappers *)\n")
            with self.assertRaisesRegex(runner.InvalidRun, "contract changed"):
                staging.references(here, runner.require, runner.fingerprint)

    def test_early_callback_and_exception_contracts_are_not_weakened(self):
        b = {e[1]: e[2] for e in observations()}
        c = {e[1]: e[2] for e in observations("reviewed")}
        for name in ("req0", "reqD", "reqD_bound1", "bound1_reqD"):
            self.assertEqual(b[name + ".construct.prims"], "2")
            self.assertEqual(c[name + ".construct.prims"], "0")
            self.assertEqual(b[name + ".construct.callbacks"], "A/A:and")
            self.assertEqual(c[name + ".construct.callbacks"], "")
            self.assertEqual(b[name + ".first.callbacks"], "")
            self.assertEqual(c[name + ".first.callbacks"], "A/A:and")
        for name in ("throw_construct", "throw_discarded"):
            self.assertEqual(b[name + ".construct.outcome"],
                             "PrinterFailure(identity=true)")
            self.assertEqual(c[name + ".construct.outcome"], "returned")
        for key in ("throw_after.first", "throw_after.second", "throw_second.second"):
            self.assertEqual(b[key + ".outcome"], "returned")
            self.assertEqual(c[key + ".outcome"], "PrinterFailure(identity=true)")

    def test_requirement_list_quirks_and_late_obligations(self):
        b = {e[1]: e[2] for e in observations()}
        self.assertEqual(b["reqD_then_plain.first.outcome"], "returned")
        self.assertIn("REQUIRE_DECREASE_TAC", b["plain_then_reqD.first.outcome"])
        self.assertIn("REQUIRE_DECREASE_TAC", b["req0_then_reqD.first.outcome"])
        self.assertEqual(b["reqD_then_req0.first.outcome"], "returned")
        self.assertIn("REQUIRE0_TAC", b["both_failure.first.outcome"])
        self.assertEqual(b["reqD_then_abbr.first.outcome"], "returned")
        self.assertIn("REQUIRE_DECREASE_TAC", b["reqD_after_abbr.first.outcome"])
        for key in ("malformed_bound", "reqD_malformed_bound"):
            self.assertEqual(b[key + ".construct.outcome"], "returned")
            self.assertEqual(b[key + ".first.outcome"], "Option(identity=true)")
        self.assertIn("No frag called", b["late_fragment.first.outcome"])
        self.assertEqual(b["late_fragment.second.outcome"], "returned")
        self.assertEqual(b["late_label.first.outcome"], "returned")
        self.assertIn("UNABBREV_TAC", b["late_abbr.second.outcome"])
        self.assertIn("A/A:and", b["grammar_context.first.outcome"])
        c = {e[1]: e[2] for e in observations("reviewed")}
        self.assertIn("B/B:and", c["grammar_context.first.outcome"])

    def test_goals_hypotheses_and_closed_proofs_are_real_observations(self):
        b = {e[1]: e[2] for e in observations()}
        self.assertEqual(b["closed.first.goals"], "")
        self.assertTrue(b["closed.first.theorem"].startswith("[]|-"))
        ordered = b["ordered_subgoals.first.goals"].split(";")
        self.assertEqual(len(ordered), 2)
        self.assertTrue(ordered[0].endswith("|-v(stage_p:min$bool[])"))
        self.assertTrue(ordered[1].endswith("|-v(stage_q:min$bool[])"))
        self.assertIn("stage_r", b["hyp_rule.first.theorem"].split("|-")[0])
        self.assertTrue(b["label_reference_order.first.goals"].endswith(
            "|-v(stage_q:min$bool[])"))
        self.assertTrue(b["label_reference_order.second.goals"].endswith(
            "|-v(stage_p:min$bool[])"))
        self.assertNotEqual(b["installed_bound1.first.goals"],
                            b["installed_bound1.second.goals"])
        self.assertNotEqual(b["bound1_two_redex.first.goals"],
                            b["bound2_two_redex.first.goals"])


class ProtocolTests(unittest.TestCase):
    def setUp(self):
        helper = test_runner.ProtocolTests()
        helper.setUp()
        self.addCleanup(helper.doCleanups)
        self.helper = helper
        private = helper.private
        (private / "Staging.sml").write_text("(* fixture *)\n")
        self.args = dict(helper.args, fixture="Staging",
                         contract=staging.expectation(runner.HERE, "baseline"))
        self.events = copy.deepcopy(helper.events[:7])
        self.events[0][2] = "Staging"
        for name in ("Traverse", "simpLib", "Staging"):
            self.events.append(["use", str(private / (name + ".sml"))])
            if name == "Staging":
                self.events.extend(observations())
            self.events.append(["used", str(private / (name + ".sml"))])
        self.events.extend(["loaded", str(private / (name + ".sml"))]
                           for name in ("Paired", "Traverse", "simpLib", "Staging"))
        self.events.append(["end", "pass", "60"])

    def test_independent_new_contract_passes_only_baseline(self):
        self.assertEqual(runner.validate(self.helper.receipt(self.events),
                                        **self.args)["outcome"], "pass")
        start = next(i for i, e in enumerate(self.events)
                     if e[:2] == ["observation", "empty.construct.prims"])
        end = next(i for i, e in enumerate(self.events)
                   if e == ["used", str(self.helper.private / "Staging.sml")])
        es = self.events[:start] + observations("reviewed") + self.events[end:]
        es[-1][-1] = "57"
        r = self.helper.receipt(es)
        with self.assertRaises(runner.InvalidRun):
            runner.validate(r, **self.args)
        args = dict(self.args, contract=staging.expectation(runner.HERE, "reviewed"))
        self.assertEqual(runner.validate(r, **args)["outcome"],
                         "expected-candidate-red")

    def test_stage_proof_and_identity_mutations_are_rejected(self):
        mutations = {
            "req0.construct.prims": "0",
            "reqD.first.callbacks": "A/A:and",
            "throw_construct.construct.outcome": "PrinterFailure(identity=false)",
            "empty.first.theorem": "[]|-wrong",
            "ordered_subgoals.first.goals": "reversed goals",
            "hyp_rule.first.theorem": "foreign hypothesis",
            "validations.executed": "0",
        }
        for key, value in mutations.items():
            with self.subTest(key=key):
                es = copy.deepcopy(self.events)
                next(e for e in es if e[1] == key)[2] = value
                with self.assertRaisesRegex(runner.InvalidRun, "ordered observations"):
                    runner.validate(self.helper.receipt(es), **self.args)

    def test_missing_second_use_and_validation_are_rejected(self):
        for key in ("reqD.second.prims", "closed.first.theorem"):
            es = [e for e in self.events if e[1] != key]
            with self.assertRaisesRegex(runner.InvalidRun, "ordered observations"):
                runner.validate(self.helper.receipt(es), **self.args)


if __name__ == "__main__":
    unittest.main()
