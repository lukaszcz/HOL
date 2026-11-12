#!/usr/bin/env python3
"""Controls for the pinned-revision skip helper (no HOL)."""
import subprocess
import tempfile
import unittest

from run_paired import HERE, require_revisions


class RevisionGuardTest(unittest.TestCase):
    def test_absent_revision_skips_naming_it(self):
        rev = "0123456789abcdef0123456789abcdef01234567"
        with self.assertRaises(unittest.SkipTest) as caught:
            require_revisions(rev)
        self.assertIn(rev, str(caught.exception))

    def test_present_revision_does_not_skip(self):
        with tempfile.TemporaryDirectory() as temp:
            def git(*args):
                return subprocess.run(["git", "-C", temp, *args], check=True,
                                      capture_output=True, text=True).stdout
            git("init", "-q")
            git("-c", "user.name=t", "-c", "user.email=t@t", "commit",
                "-q", "--allow-empty", "-m", "x")
            head = git("rev-parse", "HEAD").strip()
            require_revisions(head, repo=temp)
            blob = git("rev-parse", "HEAD^{tree}").strip()
            require_revisions(blob, repo=temp)  # a non-commit object
            with self.assertRaises(unittest.SkipTest):
                require_revisions("0" * 40, repo=temp)


if __name__ == "__main__":
    unittest.main()
