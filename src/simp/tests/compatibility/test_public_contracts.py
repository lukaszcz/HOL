#!/usr/bin/env python3
"""Public-client installation and fail-closed observation controls."""
import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

import public_contracts as public
import run_paired as runner
import test_runner


class PublicTests(unittest.TestCase):
    def setUp(self):
        self.helper = test_runner.ProtocolTests()
        self.helper.setUp()
        self.addCleanup(self.helper.doCleanups)
        self.private = self.helper.private
        self.args = dict(self.helper.args)

    def fixture(self, name, mode="pass"):
        spec = public.expectation(name, mode)
        es = copy.deepcopy(self.helper.events[:7])
        es[0][2] = name
        for sig in spec["signatures"]:
            path = self.private / (sig + ".sig")
            path.write_text("(* frozen signature *)\n")
            es.extend([["use", str(path)], ["used", str(path)]])
        for module in [*spec["modules"], name]:
            path = self.private / (module + ".sml")
            path.write_text("(* fixture *)\n")
            es.append(["use", str(path)])
            if module == name:
                if spec["red"]:
                    es.append(["exception", "Fail", r'Fail \"Static Errors\"'])
                    break
                es.extend(spec["observations"])
            es.append(["used", str(path)])
        es.append(["loaded", str(self.private / "Paired.sml")])
        es.extend(["loaded", e[1]] for e in es[:] if e[0] == "used")
        es.append(["end", "error" if spec["red"] else "pass",
                   "0" if spec["red"] else str(len(spec["checks"]))])
        r = self.helper.receipt(es)
        if spec["red"]:
            r["exit"] = 1
            r["stdout"] += "\n".join(
                str(self.private / (name + ".sml")) +
                ":9: error: Error while matching datatype reducer: constructor " +
                c + " was present in the structure but not in the signature."
                for c in ("CONFIG_REDUCER", "CONTEXT_REDUCER")) + "\n"
        return r, dict(self.args, fixture=name, contract=spec)

    def test_public_pass_requires_complete_checks(self):
        r, args = self.fixture("PublicSimpLib")
        self.assertEqual(runner.validate(r, **args)["outcome"], "pass")
        r["stdout"] = r["stdout"].replace("complete simpLib ascription", "wrong")
        with self.assertRaisesRegex(runner.InvalidRun, "ordered observations"):
            runner.validate(r, **args)

    def test_functor_red_requires_both_exact_constructor_errors(self):
        r, args = self.fixture("PublicTraverseFunctor", "reject")
        self.assertEqual(runner.validate(r, **args)["outcome"],
                         "expected-candidate-red")
        r["stdout"] = r["stdout"].replace("CONFIG_REDUCER", "OTHER")
        with self.assertRaisesRegex(runner.InvalidRun, "exact datatype rejection"):
            runner.validate(r, **args)

    def test_expected_red_does_not_hide_additional_static_errors(self):
        r, args = self.fixture("PublicTraverseFunctor", "reject")
        r["stdout"] += str(self.private / "PublicTraverseFunctor.sml") + \
            ":10: error: unrelated value has wrong type\n"
        with self.assertRaisesRegex(runner.InvalidRun, "unexpected static error"):
            runner.validate(r, **args)

    def test_exhaustiveness_is_a_separate_break(self):
        r, args = self.fixture("PublicTraverseClient", "reject")
        with self.assertRaisesRegex(runner.InvalidRun, "exhaustive REDUCER"):
            runner.validate(r, **args)
        r["stdout"] += str(self.private / "PublicTraverseClient.sml") + \
            ":9: warning: Matches are not exhaustive.\n"
        self.assertEqual(runner.validate(r, **args)["outcome"],
                         "expected-candidate-red")
        args["contract"] = public.expectation("PublicTraverseClient", "pass")
        with self.assertRaisesRegex(runner.InvalidRun, "exhaustive REDUCER"):
            runner.validate(r, **args)

    def test_ascription_cannot_skip_frozen_signature(self):
        r, args = self.fixture("PublicOpening")
        r["stdout"] = r["stdout"].replace("LegacyOpening.sig", "Other.sig")
        (self.private / "Other.sig").write_text("(* other signature *)\n")
        with self.assertRaisesRegex(runner.InvalidRun, "frozen signature not elaborated"):
            runner.validate(r, **args)

    def test_unrelated_warning_is_not_constructor_coverage(self):
        r, args = self.fixture("PublicTraverseClient", "reject")
        r["stdout"] += "/shared/Other.sml:9: warning: Matches are not exhaustive.\n"
        with self.assertRaisesRegex(runner.InvalidRun, "exhaustive REDUCER"):
            runner.validate(r, **args)

    def test_attribute_cannot_silently_use_preloaded_source(self):
        r, args = self.fixture("PublicThmAttribute")
        r["stdout"] = r["stdout"].replace(
            "preloaded\tHolKernel,Paired", "preloaded\tHolKernel,Paired,ThmAttribute")
        with self.assertRaisesRegex(runner.InvalidRun, "early module already present"):
            runner.validate(r, **args)

    def test_inventory_rejects_uncovered_baseline_signature(self):
        def git(repo, *args):
            return (b"src/simp/src/Traverse.sig\nsrc/Other.sig\n"
                    if args[0] == "ls-tree" else b"src/Other.sig\n")
        with self.assertRaisesRegex(runner.InvalidRun, "without a client"):
            public.inventory(None, "base", "candidate", {}, git, runner.require)

    def test_original_clients_cannot_be_weakened(self):
        with tempfile.TemporaryDirectory(prefix="public-seal-") as tmp:
            dst = Path(tmp)
            shutil.copytree(runner.HERE / "public", dst / "public")
            with (dst / "public/PublicTraverseFunctor.sml").open("a") as out:
                out.write("(* accommodate a candidate *)\n")
            with self.assertRaisesRegex(runner.InvalidRun, "baseline client changed"):
                public.references(dst, self.helper.repo, runner.git,
                                  runner.require, runner.fingerprint)

    def test_original_signature_installation_is_exact(self):
        runner.require_revisions(*{s["revision"] for s in json.loads(
            (runner.HERE / "public/references.json").read_text()).values()})
        with tempfile.TemporaryDirectory(prefix="public-install-") as tmp:
            dst = Path(tmp)
            (dst / "Holmakefile").write_text("")
            refs = public.references(runner.HERE, runner.HERE.parents[3],
                                     runner.git, runner.require, runner.fingerprint)
            public.install(runner.HERE, dst, refs)
            for name in refs:
                original = (runner.HERE / "inputs/develop" / (name + ".sig")).read_text()
                restored = (dst / (public.legacy_name(name) + ".sig")).read_text()
                restored = restored.replace("signature " + public.legacy_name(name) + " =",
                                            "signature " + name + " =", 1)
                self.assertEqual(restored, original)
            for target in public.CONTRACTS:
                self.assertTrue((dst / (target + ".sml")).is_file())


if __name__ == "__main__":
    unittest.main()
