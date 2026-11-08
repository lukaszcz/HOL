"""who_pays.py against a fixture tree (no HOL, no build)."""
import contextlib
import io
import os
from pathlib import Path
import stat
import tempfile
import unittest

import who_pays as w

SEQUENCE = """\
src/simp/src
src/plain
src/numheaded
!src/extra
src/boss
"""
TOOL = '#!/bin/sh\ncat "$1.deps" 2>/dev/null\n'


class Fixture:
    def __init__(self, raw):
        self.hol = Path(raw)
        (self.hol / "tools/sequences").mkdir(parents=True)
        (self.hol / "tools/sequences/upto-parallel").write_text(SEQUENCE)
        (self.hol / "sigobj").mkdir()
        (self.hol / "bin").mkdir()
        tool = self.hol / "bin/holdeptool.exe"
        tool.write_text(TOOL)
        tool.chmod(tool.stat().st_mode | stat.S_IXUSR)

    def mod(self, name, deps=()):
        (self.hol / "sigobj" / (name + ".uo")).write_text(
            "".join("%s\n" % d for d in deps))

    def src(self, rel, name, deps=(), heap="$(HOLDIR)/bin/hol.state0",
            builds=False, rules="all: $(DEFAULT_TARGETS) selftest.exe\n"):
        d = self.hol / rel
        d.mkdir(parents=True, exist_ok=True)
        (d / "Holmakefile").write_text("HOLHEAP = %s\n%s%s" % (
            heap, "\tbuildheap -o $@\n" if builds else "", rules))
        (d / name).write_text("(* source *)\n")
        (d / (name + ".deps")).write_text("\n".join(deps) + "\n")


class WhoPaysTest(unittest.TestCase):
    def tree(self, raw):
        f = Fixture(raw)
        f.mod("simpLib")
        f.mod("BasicProvers", ["simpLib"])
        f.mod("HolKernel")
        f.src("src/simp/src", "selftest.sml", ["simpLib"])
        f.src("src/plain", "aScript.sml", ["BasicProvers"])
        f.src("src/plain", "bScript.sml", ["HolKernel"])
        f.src("src/plain", "selftest.sml", ["BasicProvers", "List"])
        f.src("src/numheaded", "cScript.sml", ["simpLib"], heap="numheap",
              builds=True)
        f.src("src/extra", "dScript.sml", ["Helper"])
        f.src("src/extra", "Helper.sml", ["BasicProvers"])
        f.src("src/extra", "selftest.sml", ["HolKernel"])
        f.src("src/boss", "eScript.sml", ["simpLib"], heap="numheap")
        return f

    def test_closure_counts_split_by_build_mode(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            entries, s, problems = w.analyse(f.hol)
            self.assertEqual(problems, [])
            # aScript reaches simpLib only through BasicProvers.
            self.assertEqual(s["plain_scripts"], 1)
            self.assertEqual(s["plain_selftest_links"], 1)
            self.assertEqual(s["simp_src_selftest"], 1)
            self.assertEqual(s["numheap_builds"], 1)  # boss only uses it
            self.assertEqual(s["plain_total"], 4)
            # dScript reaches it through a module of its own directory.
            self.assertEqual(s["tflag_scripts"], 1)
            self.assertEqual(s["tflag_selftest_links"], 0)
            self.assertEqual(s["with_t_total"], 5)
            by = {e["dir"]: e for e in entries}
            self.assertEqual(by["src/plain"]["simpLib"],
                             ["aScript", "selftest"])
            self.assertTrue(by["src/extra"]["bang"])

    def test_dangling_link_is_an_error(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            (f.hol / "sigobj/BasicProvers.uo").unlink()
            os.symlink(f.hol / "nowhere.uo", f.hol / "sigobj/BasicProvers.uo")
            _, _, problems = w.analyse(f.hol)
            self.assertTrue(any("dangling" in p and "BasicProvers" in p
                                for p in problems), problems)

    def test_unknown_module_is_an_error_and_basis_names_are_not(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            f.src("src/plain", "fScript.sml", ["List", "Missing"])
            _, _, problems = w.analyse(f.hol)
            self.assertEqual(len(problems), 1, problems)
            self.assertIn("module Missing", problems[0])

    def test_main_exit_status_and_summary(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), \
                    contextlib.redirect_stderr(err):
                self.assertEqual(w.main(["who_pays", str(f.hol)]), 0)
            self.assertIn("SUMMARY\tplain_total\t4", out.getvalue())
            self.assertIn("SUMMARY\twith_t_total\t5", out.getvalue())
            f.src("src/plain", "gScript.sml", ["Missing"])
            out, err = io.StringIO(), io.StringIO()
            with contextlib.redirect_stdout(out), \
                    contextlib.redirect_stderr(err):
                self.assertEqual(w.main(["who_pays", str(f.hol)]), 2)
            self.assertIn("PROBLEM", err.getvalue())

    def test_unpinned_payer_is_an_error(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            (f.hol / "src/plain/Holmakefile").unlink()
            _, s, _ = w.analyse(f.hol)
            self.assertEqual(s["unpinned_payers"], ["src/plain"])

    def problems(self, f):
        return w.analyse(f.hol)[2]

    def test_allowlisted_name_in_sigobj_is_followed(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            f.mod("Process", ["simpLib"])
            f.src("src/plain", "hScript.sml", ["Process"])
            _, s, problems = w.analyse(f.hol)
            self.assertEqual(problems, [])
            self.assertEqual(s["plain_scripts"], 2)

    def test_allowlisted_name_that_is_a_local_module_is_refused(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            f.src("src/plain", "iScript.sml", ["Unicode"])
            self.assertEqual(self.problems(f), [])
            f.src("src/plain", "Unicode.sml", ["simpLib"])
            problems = self.problems(f)
            self.assertEqual(len(problems), 1, problems)
            self.assertIn("allowlisted in NOT_MODULES", problems[0])
            self.assertIn("Unicode", problems[0])

    def test_not_modules_is_minimal(self):
        self.assertEqual(len(w.NOT_MODULES), 20)
        for name in ("Word", "Vector", "Date", "Text"):
            self.assertNotIn(name, w.NOT_MODULES)

    def test_all_must_link_selftest_exe(self):
        cases = {
            "no all rule": "",
            "link only under the selftest level":
                "ifdef HOLSELFTESTLEVEL\nall: selftest.exe\nendif\n",
            "link in the else branch of a conditional":
                "ifeq ($(KERNELID),otknl)\nelse\nall: selftest.exe\n"
                "endif\n",
            "variable assignment": "all := selftest.exe\n",
        }
        for label, rules in cases.items():
            with tempfile.TemporaryDirectory() as raw:
                f = self.tree(raw)
                f.src("src/plain", "selftest.sml", ["BasicProvers"],
                      rules=rules)
                problems = self.problems(f)
                self.assertEqual(len(problems), 1, (label, problems))
                self.assertIn("src/plain", problems[0])
                self.assertIn("selftest.exe", problems[0])

    def test_link_forms_that_count(self):
        for rules in ("all: selftest.exe\n",
                      "all : $(DEFAULT_TARGETS) ./selftest.exe\n",
                      "all: a.uo \\\n  selftest.exe\n",
                      "ifdef POLY\nall: selftest.exe\nendif\n"):
            with tempfile.TemporaryDirectory() as raw:
                f = self.tree(raw)
                f.src("src/plain", "selftest.sml", ["BasicProvers"],
                      rules=rules)
                self.assertEqual(self.problems(f), [], rules)

    def test_link_not_needed_where_selftest_misses_simplib(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            f.src("src/plain", "selftest.sml", ["HolKernel"], rules="")
            self.assertEqual(self.problems(f), [])

    def test_simp_src_scripts_are_checked(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            f.src("src/simp/src", "okScript.sml", ["HolKernel"])
            self.assertEqual(self.problems(f), [])
            f.src("src/simp/src", "badScript.sml", ["BasicProvers"])
            problems = self.problems(f)
            self.assertEqual(len(problems), 1, problems)
            self.assertIn("src/simp/src/badScript.sml reaches simpLib",
                          problems[0])

    def test_pinned_directory_after_boss_is_refused(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            (f.hol / "tools/sequences/upto-parallel").write_text(
                SEQUENCE + "src/late\nsrc/later\n")
            f.src("src/late", "zScript.sml", ["HolKernel"],
                  heap="$(HOLDIR)/bin/hol.state")
            self.assertEqual(self.problems(f), [])
            f.src("src/later", "yScript.sml", ["HolKernel"])
            problems = self.problems(f)
            self.assertEqual(len(problems), 1, problems)
            self.assertIn("src/later comes after src/boss", problems[0])

    def test_holdeptool_failure_on_a_top_level_file_is_a_problem(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            tool = f.hol / "bin/holdeptool.exe"
            tool.write_text("#!/bin/sh\nexit 1\n")
            problems = self.problems(f)
            self.assertTrue(any("holdeptool failed" in p for p in problems))

    def test_congLib_payers_are_split_by_build_mode(self):
        with tempfile.TemporaryDirectory() as raw:
            f = self.tree(raw)
            f.mod("congLib", ["simpLib"])
            f.src("src/plain", "jScript.sml", ["congLib"])
            f.src("src/extra", "kScript.sml", ["congLib"])
            _, s, _ = w.analyse(f.hol)
            self.assertEqual((s["congLib_plain"], s["congLib_tflag"],
                              s["congLib_payers"]), (1, 1, 2))


if __name__ == "__main__":
    unittest.main()
