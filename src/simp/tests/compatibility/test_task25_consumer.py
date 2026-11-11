#!/usr/bin/env python3
"""Fail-closed controls for the isolated consumer driver (no HOL stubs)."""
import argparse
import contextlib
import io
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

DRIVER = Path(__file__).with_name("run_task25_consumer.py")
spec = importlib.util.spec_from_file_location("task25", DRIVER)
task25 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(task25)


class Controls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="task25-control-")
        self.root = Path(self.temp.name)
        self.runner = task25.Runner(self.root, self.root, self.root,
                                    self.root, self.root, self.root)

    def tearDown(self):
        self.temp.cleanup()

    def run_command(self, body, **kwargs):
        return self.runner.run("control", [sys.executable, "-c", body], **kwargs)

    def test_failed_process_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "command failed"):
            self.run_command("print('OK'); raise SystemExit(1)")
        self.assertEqual(self.runner.manifest["runs"][0]["exit"], 1)

    def test_zero_exit_static_error_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "static/runtime error"):
            self.run_command("print('error in load fixture : Static Errors')")

    def test_missing_observation_rejected(self):
        with self.assertRaisesRegex(RuntimeError, "missing marker"):
            self.run_command("print('not a test')", marker="TASK25_DONE")

    def test_success_observed(self):
        self.run_command("print('TASK25_DONE')", marker="TASK25_DONE")
        self.assertEqual(self.runner.manifest["runs"][0]["exit"], 0)

    def test_negative_test_labels_not_static_errors(self):
        self.run_command("print('failed unification restores state ... OK')",
                         marker="OK")

    def test_source_drift_rejected(self):
        source = self.root / "source.sml"
        source.write_text("original")
        expected = task25.inventory(self.root)
        source.write_text("changed")
        with self.assertRaisesRegex(RuntimeError, "source drift"):
            task25.verify(self.root, expected)

    def test_missing_source_rejected(self):
        with self.assertRaises(FileNotFoundError):
            task25.verify(self.root, {"missing.sml": {"sha256": "none"}})

    def test_nonstandard_launcher_rejected(self):
        launcher = self.root / "selftest.exe"
        launcher.write_text("#!/bin/sh\nexit 0\n")
        with self.assertRaisesRegex(RuntimeError, "nonstandard launcher"):
            self.runner.launcher(launcher, "selftest")


SHM = Path("/dev/shm")


def git(root, *args):
    done = subprocess.run(["git", "-C", str(root), *args], check=True,
                          capture_output=True, text=True,
                          env={**os.environ, "GIT_AUTHOR_NAME": "t",
                               "GIT_AUTHOR_EMAIL": "t@example.invalid",
                               "GIT_COMMITTER_NAME": "t",
                               "GIT_COMMITTER_EMAIL": "t@example.invalid"})
    return done.stdout.strip()


def commit(root, message, files):
    for name, text in files.items():
        path = root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    git(root, "add", "-A")
    git(root, "commit", "-q", "-m", message)
    return git(root, "rev-parse", "HEAD")


class FakeRepo(unittest.TestCase):
    """Tiny repository standing in for the pins: MAIN <- CAND, CONS, OTHER."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(
            prefix="task25-plan-", dir=SHM if SHM.is_dir() else None)
        self.repo = Path(self.temp.name) / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q", "-b", "main")
        (self.repo / ".gitignore").write_text("ignored/\n")
        scripts = {"src/auto/rules/n%dScript.sml" % i: "val x = [a = %d];\n" % i
                   for i in range(4)}
        self.main = commit(self.repo, "main", {
            task25.LIST: "main list\n", "tracked/f": "x\n",
            "src/auto/placeholder": "x\n", ".gitignore": "ignored/\n"})
        self.cand = commit(self.repo, "cand", {"cand": "c\n"})
        git(self.repo, "checkout", "-q", "--orphan", "cons")
        git(self.repo, "rm", "-rfq", ".")
        self.consumer = commit(self.repo, "consumer", {
            task25.LIST: "consumer list\n", "src/auto/rules/Holmakefile": "\n",
            "help/Docfiles/d": "d\n", **scripts})
        git(self.repo, "checkout", "-q", "--orphan", "other")
        git(self.repo, "rm", "-rfq", ".")
        self.other = commit(self.repo, "other", {"o": "o\n"})
        git(self.repo, "checkout", "-q", "main")
        self.patch = Path(self.temp.name) / "consumer.patch"
        self.patch.write_text(
            "diff --git a/src/auto/rules/Holmakefile "
            "b/src/auto/rules/Holmakefile\n"
            "--- a/src/auto/rules/Holmakefile\n"
            "+++ b/src/auto/rules/Holmakefile\n"
            "@@ -1 +1,2 @@\n \n+# patched\n")
        self.saved = (task25.MAIN, task25.CONSUMER, task25.PATCH_SHA256)
        task25.MAIN, task25.CONSUMER = self.main, self.consumer
        task25.PATCH_SHA256 = task25.sha(self.patch.read_bytes())

    def tearDown(self):
        task25.MAIN, task25.CONSUMER, task25.PATCH_SHA256 = self.saved
        self.temp.cleanup()

    def args(self, **over):
        values = dict(consumer_patch=self.patch, patch_sha256=None,
                      consumer_revision=self.consumer,
                      simplifier_revision=self.main, alias=None,
                      scratch=None, jobs=None, skip_routine=False)
        values.update(over)
        return argparse.Namespace(**values)

    def plan(self, **over):
        return task25.plan(self.args(**over), self.repo)


class Plan(FakeRepo):
    def test_defaults_are_the_pins(self):
        got = self.plan()
        self.assertEqual(got["simplifier"], self.main)
        self.assertFalse(got["patch_pin_overridden"])
        self.assertNotIn("scratch", got)
        self.assertNotIn("alias", got)

    def test_descendant_resolved_to_full_hash(self):
        got = self.plan(simplifier_revision=self.cand[:12])
        self.assertEqual(got["simplifier"], self.cand)

    def test_missing_revision_refused(self):
        with self.assertRaisesRegex(RuntimeError, "unknown revision"):
            self.plan(simplifier_revision="no-such-revision")

    def test_option_like_revision_refused(self):
        with self.assertRaisesRegex(RuntimeError, "bad revision"):
            self.plan(simplifier_revision="--all")

    def test_unrelated_revision_refused(self):
        with self.assertRaisesRegex(RuntimeError, "does not descend"):
            self.plan(simplifier_revision=self.other)

    def test_wrong_consumer_revision_refused(self):
        with self.assertRaisesRegex(RuntimeError, "pinned prerequisite"):
            self.plan(consumer_revision=self.cand)

    def test_wrong_patch_hash_refused(self):
        self.patch.write_text(self.patch.read_text() + "+# more\n")
        with self.assertRaisesRegex(RuntimeError, "patch sha256 mismatch"):
            self.plan()

    def test_reviewed_patch_override(self):
        self.patch.write_text(self.patch.read_text() + "+# more\n")
        digest = task25.sha(self.patch.read_bytes())
        got = self.plan(patch_sha256=digest)
        self.assertTrue(got["patch_pin_overridden"])
        with self.assertRaisesRegex(RuntimeError, "bad --patch-sha256"):
            self.plan(patch_sha256="abc")

    def test_missing_patch_refused(self):
        with self.assertRaisesRegex(RuntimeError, "missing consumer patch"):
            self.plan(consumer_patch=self.patch.with_name("none"))

    def test_real_pin_is_the_checked_in_patch(self):
        real = DRIVER.parent / "consumer/consumer.patch"
        self.assertEqual(task25.sha(real.read_bytes()), self.saved[2])

    def test_jobs_must_be_positive(self):
        with self.assertRaisesRegex(RuntimeError, "--jobs"):
            self.plan(jobs=0)

    def test_alias_must_be_explicit_normalized(self):
        self.assertEqual(self.plan(alias=Path("/dev/shm/a"))["alias"],
                         Path("/dev/shm/a"))
        for bad in ("rel/alias", "/dev/shm/a/../b", "/"):
            with self.assertRaisesRegex(RuntimeError, "--alias"):
                self.plan(alias=Path(bad))

    def test_scratch_refusals(self):
        for bad, why in ((Path("rel/scratch"), "absolute"),
                         (Path("/tmp/t32-s3-x"), "/tmp"),
                         (Path("/var/tmp/t32-s3-x"), "/tmp"),
                         (self.repo / "tracked/new", "tracked tree"),
                         (self.repo / "untracked-unignored", "not ignored")):
            with self.subTest(bad=str(bad)):
                with self.assertRaisesRegex(RuntimeError, why):
                    self.plan(scratch=bad)

    def test_scratch_existing_refused(self):
        with self.assertRaisesRegex(RuntimeError, "already exists"):
            (self.repo / "ignored").mkdir()
            self.plan(scratch=self.repo / "ignored")

    def test_scratch_containing_repo_refused(self):
        with self.assertRaisesRegex(RuntimeError, "contains caller"):
            self.plan(scratch=self.repo.parent)

    @unittest.skipUnless(SHM.is_dir(), "no /dev/shm")
    def test_scratch_in_shm_and_in_ignored_accepted(self):
        got = self.plan(scratch=SHM / "t32-s3-unit-none")
        self.assertEqual(got["scratch"], SHM / "t32-s3-unit-none")
        got = self.plan(scratch=self.repo / "ignored/deep/scratch")
        self.assertEqual(got["scratch"], self.repo / "ignored/deep/scratch")

    def test_output_inside_tracked_tree_refused(self):
        with self.assertRaisesRegex(RuntimeError, "tracked tree"):
            task25.outside_tracked(self.repo, self.repo / "tracked/o", "output")
        task25.outside_tracked(self.repo, self.repo / "ignored/o", "output")

    def test_alias_mismatch_refused(self):
        core = self.repo.parent / "core"
        (core / "tools/Holmake").mkdir(parents=True)
        (core / "tools/Holmake/Systeml.sml").write_text(
            'val HOLDIR = "/dev/shm/one"\n')
        task25.check_configured_alias(core, Path("/dev/shm/one"))
        with self.assertRaisesRegex(RuntimeError, "different alias"):
            task25.check_configured_alias(core, Path("/dev/shm/two"))


class Commands(unittest.TestCase):
    def test_default_is_task25_sequence(self):
        self.assertEqual(
            task25.build_commands(None, False),
            [("bootstrap", ["bin/build", task25.SEQUENCE]),
             ("routine", ["bin/build", "-t", task25.SEQUENCE])])

    def test_jobs_and_skip_routine(self):
        self.assertEqual(
            task25.build_commands(8, True),
            [("bootstrap", ["bin/build", "-j8", task25.SEQUENCE])])
        self.assertEqual(task25.build_commands(8, False)[1][1],
                         ["bin/build", "-t", "-j8", task25.SEQUENCE])


class Sandbox(FakeRepo):
    def test_scratch_bound_after_repo_readonly(self):
        runner = task25.Runner(self.repo, self.repo, self.repo / "ignored/s",
                               Path("/dev/shm/a"), self.repo / "ignored/s/core",
                               self.repo / "ignored/s/consumer")
        runner.git_common = self.repo / ".git"
        cmd = runner.sandbox(["true"])
        ro = cmd.index(str(self.repo), cmd.index("--ro-bind", 8))
        scratch = cmd.index(str(self.repo / "ignored/s"))
        self.assertLess(ro, scratch)


@unittest.skipUnless(SHM.is_dir(), "no /dev/shm")
class PrepareOnly(FakeRepo):
    """Whole driver, prepare-only: no build process, real git and patch."""

    def run_main(self, *extra, revision=None):
        out = Path(self.temp.name) / "out"
        scratch = SHM / ("t32-s3-unit-%d" % os.getpid())
        self.addCleanup(lambda: scratch.exists() and
                        __import__("shutil").rmtree(scratch))
        argv = ["driver", "--consumer-patch", str(self.patch),
                "--output", str(out), "--prepare-only",
                "--simplifier-revision", revision or self.cand,
                "--alias", "/dev/shm/t32-s3-unit-alias",
                "--scratch", str(scratch), *extra]
        saved = (sys.argv, task25.__file__)
        sys.argv = argv
        fake = self.repo / "a/b/c/d/driver.py"
        fake.parent.mkdir(parents=True)
        fake.write_text("#\n")
        task25.__file__ = str(fake)
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                task25.main()
        finally:
            sys.argv, task25.__file__ = saved
        manifest = json.loads((out / "manifest.json").read_text())
        return manifest, scratch

    def test_provenance_and_cleanup(self):
        m, scratch = self.run_main()
        self.assertTrue(m["success"])
        self.assertEqual(m["simplifier_revision"], self.cand)
        self.assertEqual(m["consumer_revision"], self.consumer)
        self.assertEqual(m["patch_sha256"], task25.PATCH_SHA256)
        self.assertEqual(m["core_prerequisite"]["blob"],
                         git(self.repo, "rev-parse",
                             self.consumer + ":" + task25.LIST))
        self.assertTrue(m["scratch_explicit"] and m["alias_explicit"])
        self.assertTrue(m["task_scratch_removed"])
        self.assertFalse(scratch.exists())

    def test_wrong_revision_leaves_no_output(self):
        out = Path(self.temp.name) / "out"
        with self.assertRaisesRegex(RuntimeError, "does not descend"):
            self.run_main(revision=self.other)
        self.assertFalse(out.exists())


if __name__ == "__main__":
    unittest.main(verbosity=2)
