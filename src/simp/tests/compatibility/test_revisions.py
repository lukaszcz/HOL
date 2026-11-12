#!/usr/bin/env python3
"""Controls for the pinned-revision skip helper (no HOL)."""
import os
import subprocess
import tempfile
import unittest

from run_paired import require_revisions


class RevisionGuardTest(unittest.TestCase):
    def test_absent_revision_skips_naming_it(self):
        rev = "0123456789abcdef0123456789abcdef01234567"
        with self.assertRaises(unittest.SkipTest) as caught:
            require_revisions(rev)
        self.assertIn(rev, str(caught.exception))

    def test_present_revision_does_not_skip(self):
        with tempfile.TemporaryDirectory() as temp:
            def git(*args):
                return subprocess.run(
                    ["git", "-C", temp, *args], check=True, text=True,
                    capture_output=True,
                    env={**os.environ, "GIT_CONFIG_GLOBAL": "/dev/null",
                         "GIT_CONFIG_NOSYSTEM": "1",
                         "GIT_AUTHOR_NAME": "t",
                         "GIT_AUTHOR_EMAIL": "t@example.invalid",
                         "GIT_COMMITTER_NAME": "t",
                         "GIT_COMMITTER_EMAIL": "t@example.invalid"}).stdout
            git("init", "-q")
            git("commit", "-q", "--allow-empty", "-m", "x")
            head = git("rev-parse", "HEAD").strip()
            require_revisions(head, repo=temp)
            tree = git("rev-parse", "HEAD^{tree}").strip()
            require_revisions(tree, repo=temp)  # a non-commit object
            with self.assertRaises(unittest.SkipTest):
                require_revisions("0" * 40, repo=temp)


if __name__ == "__main__":
    unittest.main()
