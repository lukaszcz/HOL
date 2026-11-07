#!/usr/bin/env python3
"""TASK31 startup gate: protocol, decision rule and build recipe.

Synthetic fixtures only: no runtime, toolchain or HOL tree is needed. Every
guard of the decision rule is killed by a case below.
"""
import copy
import os
from unittest import mock
from pathlib import Path
import subprocess
import tempfile
import unittest

import allocation_schema as sc
import startup_gate as g

HERE = Path(__file__).resolve().parent
LIB = "/synthetic/libpolyml.so.16"
HOLDIR = "/synthetic/b1/hol-source"
MODULES = ["Array", "bossLib", "boolLib"]
FILES = ["bossLib.sml", "boolLib.sml"]
STRUCTS = ["bossLib", "boolLib", "simpLib"]


def snap(total=100, native=90, rts=8, interp=0, code=2, abi=1, over=0):
    return [abi, 8, over, total, native, rts, interp, code]


def stdout(kind="hol-startup", brackets=None, loaded=MODULES, files=FILES,
           structs=STRUCTS, holdir=HOLDIR, foreign="0,0", result="none",
           end=True, lib=LIB):
    brackets = brackets or [("startup", snap(), snap()),
                            ("empty", snap(), snap(104, 94))]
    lines = []
    for name, s, e in brackets:
        lines.append("\t".join(["@@GATE", kind, "alloc", name,
                                ",".join(map(str, s)) + ";" +
                                ",".join(map(str, e))]))
    rows = [("holdir", "path", holdir), ("foreign", "path", foreign),
            ("result", "none" if result == "none" else "ok",
             "-" if result == "none" else result),
            ("loaded", "count", str(len(loaded))),
            ("loaded", "modules", ",".join(loaded)),
            ("files", "count", str(len(files))),
            ("files", "names", ",".join(files)),
            ("structures", "count", str(len(structs))),
            ("structures", "names", ",".join(structs))]
    for event, name, payload in rows:
        lines.append("\t".join(["@@GATE", kind, event, name, payload]))
    lines.append("@@TASK29_ALLOC_RUNTIME_V1\t" + lib)
    lines.append("@@TASK29_ALLOC_MAP_V1\t0-1 r-xp 0 00:00 1 " + lib)
    if end:
        lines.append("@@GATE\tend")
    return "\n".join(lines) + "\n"


def parse(**kw):
    kind = kw.get("kind", "hol-startup")
    return g.parse_process(stdout(**kw), kind, HOLDIR, LIB, ())


class ParseTest(unittest.TestCase):
    def test_valid(self):
        record = parse()
        self.assertEqual(record["loaded"], MODULES)
        self.assertEqual(g.bracket_fields(record["brackets"][0])["total"],
                         100)
        self.assertEqual(g.bracket_fields(record["brackets"][1])["total"], 4)

    def rejects(self, message, **kw):
        with self.assertRaisesRegex(sc.InvalidAllocation, message):
            parse(**kw)

    def test_guards(self):
        self.rejects("did not finish", end=False)
        self.rejects("wrong HOLDIR", holdir="/other/hol-source")
        self.rejects("foreign-thread", foreign="1,0")
        self.rejects("ABI", brackets=[
            ("startup", snap(abi=2), snap()), ("empty", snap(), snap())])
        self.rejects("overflow", brackets=[
            ("startup", snap(), snap()), ("empty", snap(), snap(over=1))])
        self.rejects("first brackets", brackets=[
            ("empty", snap(), snap()), ("startup", snap(), snap())])
        self.rejects("wrong runtime|snapshot symbol", lib="/other/lib.so")
        self.rejects("malformed counter", brackets=[
            ("startup", snap(), snap()), ("empty", [1, 2], snap())])

    def test_count_mismatch(self):
        text = stdout().replace("\tloaded\tcount\t3", "\tloaded\tcount\t4")
        with self.assertRaisesRegex(sc.InvalidAllocation, "count mismatch"):
            g.parse_process(text, "hol-startup", HOLDIR, LIB, ())


def record(kind, side, pair, experiment, total=100, extra=0, **kw):
    brackets = [("startup", snap(total + extra, 90 + extra), snap()),
                ("empty", snap(), snap(104, 94))]
    if kind.startswith("load"):
        brackets.append(("load_x", snap(), snap(1000 + extra, 900 + extra)))
    r = g.parse_process(
        stdout(kind=kind, brackets=brackets,
               result="true" if kind in g.USES_SIMP else "none", **kw),
        kind, HOLDIR, LIB, ())
    r.update(side=side, pair=pair, experiment=experiment)
    return r


def grid(kinds=("hol-startup", "load-simpLib"), pairs=10, delta=None):
    """Records for every side; delta maps (kind, side) to extra words."""
    out, delta = [], delta or {}
    for kind in kinds:
        for pair in range(pairs):
            for exp, sides in (("candidate", ("base", "candidate")),
                               ("control", ("base", "control")),
                               ("repeat", ("candidate", "repeat"))):
                for side in sides:
                    out.append(record(kind, side, pair, exp,
                                      extra=delta.get((kind, side), 0)))
    return out


class DecisionTest(unittest.TestCase):
    def test_exact_zero_passes(self):
        report = g.analyse(grid(), 10)
        self.assertEqual(report["decision"], "pass", report["reasons"])
        self.assertEqual(report["experiments"]["candidate"]["kinds"][
            "hol-startup"]["nonzero_pairs"], 0)

    def test_one_word_fails_with_delta(self):
        report = g.analyse(grid(delta={("load-simpLib", "candidate"): 1}), 10)
        self.assertEqual(report["decision"], "fail")
        row = report["experiments"]["candidate"]["kinds"]["load-simpLib"]
        self.assertEqual(row["first_nonzero"]["startup"]["total"], 1)
        self.assertEqual(row["nonzero_pairs"], 10)
        self.assertIn("load_x", row["first_nonzero"])

    def test_control_must_be_zero(self):
        report = g.analyse(grid(delta={("hol-startup", "control"): 9}), 10)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any(r.startswith("control hol-startup")
                            for r in report["reasons"]))

    def test_nondeterminism_fails(self):
        records = grid()
        records[0] = record("hol-startup", "base", 0, "candidate", extra=3)
        report = g.analyse(records, 10)
        self.assertEqual(report["decision"], "fail")
        self.assertTrue(any("nondeterministic" in r
                            for r in report["reasons"]))

    def test_fewer_pairs_is_smoke(self):
        report = g.analyse(grid(pairs=4), 4)
        self.assertEqual(report["decision"], "smoke")
        self.assertFalse(report["acceptance_pairs"])

    def test_extension_module_fails(self):
        records = grid()
        for r in records:
            if r["side"] == "candidate":
                r["loaded"] = MODULES + ["SimpTracking"]
        report = g.analyse(records, 10)
        self.assertEqual(report["decision"], "fail")
        self.assertEqual(report["extension"]["hol-startup/candidate"],
                         ["module SimpTracking"])
        self.assertEqual(report["loaded_diff"]["hol-startup"]["modules"],
                         dict(only_left=[], only_right=["SimpTracking"]))

    def test_extension_structure_fails(self):
        records = grid()
        for r in records:
            if r["side"] == "candidate":
                r["structures"] = STRUCTS + ["simpExtLib"]
        self.assertEqual(g.analyse(records, 10)["decision"], "fail")

    def test_extension_allowed_when_baseline_has_it(self):
        records = grid()
        for r in records:
            r["loaded"] = MODULES + ["SimpTracking"]
        self.assertEqual(g.analyse(records, 10)["decision"], "pass")

    def test_wrong_simplifier_result_fails(self):
        records = grid()
        records[-1]["result"] = "false"
        self.assertEqual(g.analyse(records, 10)["decision"], "fail")

    def test_attribution_alone_does_not_fail(self):
        records = grid(kinds=("hol-startup", "files-simpLib"))
        for r in records:
            if r["kind"] == "files-simpLib" and r["side"] == "candidate":
                r["brackets"].append(dict(
                    name="$HOLDIR/Only.sml", start=snap(0, 0, 0, 0, 0),
                    end=snap(9, 9, 0, 0, 0)))
        report = g.analyse(records, 10)
        self.assertEqual(report["decision"], "pass", report["reasons"])
        self.assertIn("$HOLDIR/Only.sml", report["experiments"]["candidate"][
            "kinds"]["files-simpLib"]["first"])

    def test_missing_bracket_fails_a_gated_kind(self):
        records = grid()
        for r in records:
            if r["kind"] == "load-simpLib" and r["side"] == "candidate":
                r["brackets"] = r["brackets"][:2]
        self.assertEqual(g.analyse(copy.deepcopy(records), 10)["decision"],
                         "fail")

    def test_unpaired_records_refused(self):
        records = [r for r in grid() if not (
            r["experiment"] == "control" and r["side"] == "control" and
            r["pair"] == 3)]
        with self.assertRaisesRegex(sc.InvalidAllocation, "unpaired"):
            g.analyse(records, 10)

    def test_render_and_replay_stable(self):
        report = g.analyse(grid(delta={("load-simpLib", "candidate"): 7}), 10)
        text = g.render(report, {})
        self.assertIn("| load-simpLib | startup | total | 7 | 0 |", text)
        self.assertEqual(g.render(report, {}), text)


class ExtensionNames(unittest.TestCase):
    def test_names(self):
        for name in ("simpExtLib", "congExtLib", "SimpTracking",
                     "intReduceExt", "Cond_rewrExt", "numSimpsExt"):
            self.assertTrue(g.is_extension(name), name)
        for name in ("simpLib", "congLib", "Cond_rewr", "boolSimps", "Text"):
            self.assertFalse(g.is_extension(name), name)
        self.assertFalse(g.is_extension("SimpTracking", ("SimpTracking",)))


class RecipeTest(unittest.TestCase):
    def test_command_lines(self):
        client = Path("/c/StartupGate.sml")
        self.assertEqual(
            g.command("/h", "hol-startup", client),
            ["/h/bin/hol", "--gcthreads=1", "run", str(client)])
        self.assertEqual(
            g.command("/h", "load-simpLib", client),
            ["/h/bin/hol", "--gcthreads=1", "run",
             "--holstate=/h/bin/hol.state0", str(client)])

    def test_tree_spec(self):
        self.assertEqual(g.split_tree("b1=abc")[:2], ("b1", "abc"))
        with self.assertRaises(sc.InvalidAllocation):
            g.split_tree("=abc")

    def test_hol_build_commands(self):
        """The commands of bootstrap_probe.build_native_hol, in order, in a
        fresh clone: no cache, HOME, the include override, one HOLDIR, and
        a recorded patch applied only after a check."""
        with tempfile.TemporaryDirectory() as raw:
            t = Path(raw)
            repo = t / "repo"
            (repo / "tools-poly").mkdir(parents=True)
            (repo / "f.txt").write_text("one\n")
            (repo / "tools-poly/keep").write_text("k\n")
            git = lambda *c, cwd=repo: subprocess.run(
                ["git", *c], cwd=cwd, check=True, capture_output=True)
            git("init", "-q")
            git("add", ".")
            git("-c", "user.name=t", "-c", "user.email=t@t", "commit",
                "-qm", "x")
            patch = t / "p.patch"
            (repo / "f.txt").write_text("two\n")
            patch.write_bytes(subprocess.run(
                ["git", "diff"], cwd=repo, check=True,
                capture_output=True).stdout)
            git("checkout", "-q", "f.txt")
            seen = []

            def run(cmd, cwd=None, runtime_env=None):
                seen.append((cmd, runtime_env))
                if cmd[0] == "git":
                    subprocess.run(cmd, cwd=cwd, check=True,
                                   capture_output=True)
                if cmd[0].endswith("bin/build"):
                    (Path(cwd) / "bin").mkdir()
                    for n in ("hol", "hol.state0", "hol.state", "Holmake"):
                        (Path(cwd) / "bin" / n).write_text(n)
                return {"stdout": ""}
            env = g.tool_env(t)
            hol, prefix = t / "h" / "hol-source", t / "native-install"
            hol.parent.mkdir()
            report = {}
            with mock.patch.dict(os.environ,
                                 GATE_BUILD_DETERMINISTIC="0"):
                g.build_hol(repo, "HEAD", hol, prefix, env, run, report,
                            patch)
            self.assertEqual((hol / "f.txt").read_text(), "two\n")
            commands = [c for c, _ in seen]
            self.assertEqual(commands[0][:4],
                             ["git", "clone", "--shared", "--no-checkout"])
            self.assertEqual(commands[2][:3], ["git", "apply", "--check"])
            self.assertEqual(commands[3][:2], ["git", "apply"])
            self.assertEqual(commands[4], [
                str(prefix / "bin/poly"), "--error-exit", "--use",
                "tools/smart-configure.sml"])
            self.assertEqual(commands[5], [
                str(hol / "bin/build"), "--no-cache", "-j2",
                "--seq=tools/sequences/upto-parallel"])
            for _, command_env in seen[4:]:
                self.assertEqual(command_env["HOLDIR"], str(hol))
                self.assertEqual(command_env["HOME"], "/nonexistent")
            self.assertEqual((hol / "tools-poly/poly-includes.ML").read_text(),
                             'val poly = "%s";\nval polymllibdir = "%s";\n'
                             % (prefix / "bin/poly", prefix / "lib"))
            self.assertEqual(report["hol_snapshot"], report["hol_snapshot"])
            self.assertIsNotNone(report["hol_patch"])

    def test_determinism_edits_touch_image_creation_only(self):
        with tempfile.TemporaryDirectory() as t:
            hol = Path(t)
            subprocess.run(["git", "init", "-q", str(hol)], check=True)
            for name, old, _ in g.DETERMINISM:
                path = hol / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("x\n" + old + "y\n")
            subprocess.run(["git", "-C", str(hol), "add", "-A"], check=True)
            subprocess.run(["git", "-C", str(hol), "-c", "user.name=t",
                            "-c", "user.email=t@t", "commit", "-qm", "m"],
                           check=True)
            diff = g.make_deterministic(hol, None)
            self.assertIn("PolyML.fullGC", diff)
            self.assertEqual(diff.count("--gcthreads=1 buildheap"), 3)
            self.assertEqual(
                sorted(n for n, _, _ in g.DETERMINISM),
                ["src/boss/Holmakefile", "src/num/termination/Holmakefile",
                 "src/proofman/Holmakefile", "tools-poly/hol.ML"])

    def test_mktool_patch_is_build_tooling_only(self):
        text = (HERE / "startup_gate_mktool.patch").read_text()
        files = [l.split()[-1] for l in text.splitlines()
                 if l.startswith("+++ ")]
        self.assertEqual(files, ["b/src/portableML/rawtheory/mktool.ML"])


class StyleTest(unittest.TestCase):
    def test_files(self):
        for name in ("startup_gate.py", "test_startup_gate.py",
                     "StartupGate.sml", "StartupGateUse.sml",
                     "startup_gate_mktool.patch"):
            for number, line in enumerate(
                    (HERE / name).read_text().split("\n"), 1):
                where = "%s:%d" % (name, number)
                self.assertNotIn("\t", line, where)
                if not name.endswith(".patch"):  # a context line is " "
                    self.assertEqual(line, line.rstrip(), where)
                    self.assertLess(len(line), 80, where)


if __name__ == "__main__":
    unittest.main()
