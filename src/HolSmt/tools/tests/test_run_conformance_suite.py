#!/usr/bin/env python3

import json
import os
import pathlib
import stat
import sys
import tempfile
import textwrap
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

import run_conformance_suite as conformance


def make_fake_z3(directory, proof_rule="asserted"):
    path = pathlib.Path(directory) / "fake-z3"
    script = f"""#!/usr/bin/env python3
import pathlib
import sys

if "-version" in sys.argv:
    print("Z3 version 4.13.0")
    raise SystemExit(0)

input_path = pathlib.Path(sys.argv[-1])
text = input_path.read_text(encoding="utf-8")
is_unsat = "(assert false)" in text or "(not " in text
print("unsat" if is_unsat else "sat")
if is_unsat and "(get-proof" in text:
    print("(proof ({proof_rule} false))")
"""
    path.write_text(script, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)
    return path


class ConformanceSuiteTests(unittest.TestCase):
    def test_default_suite_represents_every_official_logic(self):
        cases = conformance.default_cases(None)
        represented = {case.logic for case in cases}
        self.assertFalse(set(conformance.OFFICIAL_LOGICS) - represented)
        self.assertIn("ALL", represented)
        self.assertTrue(any("metamorphic" in case.tags for case in cases))

    def test_external_benchmark_dir_and_unsupported_mode_are_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            bench_dir = root / "bench"
            bench_dir.mkdir()
            (bench_dir / "case.smt2").write_text(
                "(set-logic QF_LIA)\n(assert true)\n(check-sat)\n",
                encoding="utf-8",
            )
            out_dir = root / "out"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--no-default-suite",
                    "--benchmark-dir",
                    str(bench_dir),
                    "--mode",
                    conformance.MODE_PARSER,
                    "--mode",
                    conformance.MODE_TYPECHECK,
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            qf_lia = report["summary"]["by_logic_mode"]["QF_LIA"]
            self.assertEqual(qf_lia[conformance.MODE_PARSER]["pass"], 1)
            self.assertEqual(qf_lia[conformance.MODE_TYPECHECK]["unsupported"], 1)
            self.assertIn("no typecheck-only command configured", "\n".join(report["summary"]["unsupported_reasons"]))

    def test_proof_replay_failure_preserves_repro_input_and_raw_proof(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            fake_z3 = make_fake_z3(root, proof_rule="mystery-rule")
            out_dir = root / "out"

            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--z3",
                    str(fake_z3),
                    "--logic",
                    "QF_UF",
                    "--mode",
                    conformance.MODE_PARSER,
                    "--mode",
                    conformance.MODE_PROOF_PARSE,
                    "--mode",
                    conformance.MODE_PROOF_REPLAY,
                ]
            )

            self.assertEqual(code, 1)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            qf_uf_replay = report["summary"]["by_logic_mode"]["QF_UF"][conformance.MODE_PROOF_REPLAY]
            self.assertGreater(qf_uf_replay["fail"], 0)
            repro_inputs = list((out_dir / "repro").rglob("input.smt2"))
            repro_proofs = list((out_dir / "repro").rglob("proof.raw"))
            self.assertTrue(repro_inputs)
            self.assertTrue(repro_proofs)
            self.assertIn("mystery-rule", repro_proofs[0].read_text(encoding="utf-8"))

    def test_configured_command_mode_passes_command_context(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            checker = root / "checker.py"
            checker.write_text(
                textwrap.dedent(
                    """\
                    import pathlib
                    import sys

                    path = pathlib.Path(sys.argv[1])
                    logic = sys.argv[2]
                    assert path.read_text(encoding="utf-8").startswith(f"(set-logic {logic})")
                    """
                ),
                encoding="utf-8",
            )
            out_dir = root / "out"
            code = conformance.main(
                [
                    "--out",
                    str(out_dir),
                    "--logic",
                    "QF_UF",
                    "--mode",
                    conformance.MODE_TYPECHECK,
                    "--typecheck-command",
                    f"{sys.executable} {checker} {{input}} {{logic}}",
                ]
            )

            self.assertEqual(code, 0)
            report = json.loads((out_dir / "conformance.json").read_text(encoding="utf-8"))
            qf_uf = report["summary"]["by_logic_mode"]["QF_UF"][conformance.MODE_TYPECHECK]
            self.assertGreater(qf_uf["pass"], 0)
            self.assertEqual(qf_uf["fail"], 0)


if __name__ == "__main__":
    unittest.main()
