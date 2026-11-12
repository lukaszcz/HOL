#!/usr/bin/env python3
"""Controls for the TASK23 negative's source-isolation check (no HOL)."""
import os
from pathlib import Path
import tempfile
import unittest

from run_task23_lifecycle import negative_isolation_problems

REPO = "/r"
SRC = Path(REPO + "/src/simp/src")
PRIVATE = Path("/tmp/simp-task23-x/negative")
P = "OBS repair.loaded.path="


def lines(*paths):
    return "".join(P + p + "\n" for p in paths)


# Shaped like the real negative run: kernel modules, then the private copy.
REAL = lines(REPO + "/src/portableML/AList.sig",
             REPO + "/src/prekernel/Context.sml",
             str(PRIVATE / "SplitData.sig"),
             str(PRIVATE / "SplitData.sml"),
             REPO + "/src/parse/typecheck_error.sml") + "OBS repair=pass\n"


class IsolationTest(unittest.TestCase):
    def problems(self, text, src=SRC):
        return negative_isolation_problems(text, src, PRIVATE)

    def test_real_shaped_log_passes(self):
        self.assertEqual(self.problems(REAL), [])

    def test_sigobj_style_paths_pass(self):
        text = REAL + lines(REPO + "/sigobj/Overlay.sml",
                            REPO + "/sigobj/boolTheory.sig")
        self.assertEqual(self.problems(text), [])

    def test_production_splitlib_fails(self):
        text = REAL + lines(str(SRC / "splitLib.sig"),
                            str(SRC / "splitLib.sml"))
        found = self.problems(text)
        self.assertEqual(len(found), 1)
        self.assertIn("negative loaded production src/simp/src", found[0])
        self.assertIn("splitLib.sml", found[0])

    def test_production_splitdata_sig_alone_fails(self):
        found = self.problems(REAL + lines(str(SRC / "SplitData.sig")))
        self.assertEqual(len(found), 1)
        self.assertIn("SplitData.sig", found[0])

    def test_missing_private_splitdata_fails(self):
        text = REAL.replace(str(PRIVATE / "SplitData.sml"), "/x/Other.sml")
        found = self.problems(text)
        self.assertTrue(any("SplitData.sml" in f and "private" in f
                            for f in found))
        self.assertEqual(len(self.problems("")), 1)

    def test_symlinked_src_spelling_fails(self):
        with tempfile.TemporaryDirectory() as temp:
            real_src = Path(temp) / "real/src/simp/src"
            real_src.mkdir(parents=True)
            link = Path(temp) / "link"
            os.symlink(real_src, link)
            text = REAL + lines(str(link / "splitLib.sml"))
            # The log spells the path through the link, `src` the real way
            # and the other way round: both must be caught.
            self.assertTrue(any("production" in f
                                for f in self.problems(text, real_src)))
            text = REAL + lines(str(real_src / "splitLib.sml"))
            self.assertTrue(any("production" in f
                                for f in self.problems(text, link)))

    def test_private_sig_replaced_by_production_fails(self):
        text = REAL.replace(str(PRIVATE / "SplitData.sig"),
                            str(SRC / "SplitData.sig"))
        found = self.problems(text)
        self.assertEqual(len(found), 2)
        self.assertIn("private SplitData.sig", found[0])
        self.assertIn("production src/simp/src", found[1])

    def test_symlinked_private_dir_passes(self):
        with tempfile.TemporaryDirectory() as temp:
            real_dir = Path(temp) / "negative"
            real_dir.mkdir()
            link = Path(temp) / "link"
            os.symlink(real_dir, link)
            text = lines(str(real_dir / "SplitData.sig"),
                         str(real_dir / "SplitData.sml"))
            self.assertEqual(
                negative_isolation_problems(text, SRC, link), [])

    def test_component_boundary(self):
        text = REAL + lines(REPO + "/src/simp/src2/x.sml")
        self.assertEqual(self.problems(text), [])

    def test_relative_path_reported(self):
        found = self.problems(REAL + lines("src/simp/src/splitLib.sml"))
        self.assertEqual(len(found), 1)
        self.assertIn("non-absolute", found[0])
        self.assertIn("'src/simp/src/splitLib.sml'", found[0])


if __name__ == "__main__":
    unittest.main()
