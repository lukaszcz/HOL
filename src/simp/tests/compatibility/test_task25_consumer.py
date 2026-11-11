#!/usr/bin/env python3
"""Fail-closed controls for the isolated consumer driver (no HOL stubs)."""
import argparse
import contextlib
import gzip
import io
import importlib.util
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

DRIVER = Path(__file__).with_name("run_task25_consumer.py")
spec = importlib.util.spec_from_file_location("task25", DRIVER)
task25 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(task25)


SHM = Path("/dev/shm")
NO_SHM = "no /dev/shm: the fixtures must not fall back to /tmp"


@unittest.skipUnless(SHM.is_dir(), NO_SHM)
class Controls(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="task25-control-",
                                                dir=SHM)
        self.root = Path(self.temp.name)
        self.runner = task25.Runner(self.root, self.root, self.root,
                                    self.root, self.root, self.root)

    def tearDown(self):
        self.temp.cleanup()

    def run_command(self, body, **kwargs):
        return self.runner.run("control", [sys.executable, "-c", body],
                               **kwargs)

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

    def test_logs_compressed_with_both_hashes(self):
        self.run_command("print('TASK25_DONE')", marker="TASK25_DONE")
        record = self.runner.manifest["runs"][0]
        packed = self.root / record["log"]
        self.assertTrue(record["log"].endswith(".log.gz"))
        self.assertTrue(packed.is_file())
        self.assertFalse(packed.with_suffix("").exists())
        raw = gzip.decompress(packed.read_bytes())
        self.assertEqual(record["output"]["sha256"], task25.sha(raw))
        self.assertEqual(record["output"]["bytes"], len(raw))
        self.assertEqual(record["log_gz"], task25.fingerprint(packed))
        self.assertIn(b"TASK25_DONE", raw)

    def test_failed_command_log_also_compressed(self):
        with self.assertRaises(RuntimeError):
            self.run_command("raise SystemExit(3)")
        record = self.runner.manifest["runs"][0]
        self.assertTrue((self.root / record["log"]).is_file())
        self.assertEqual(list(self.root.glob("*.log")), [])

    def test_git_ceiling_is_the_scratch(self):
        self.run_command("import os; print(os.environ["
                         "'GIT_CEILING_DIRECTORIES'])", marker=str(self.root))

    def test_nonstandard_launcher_rejected(self):
        launcher = self.root / "selftest.exe"
        launcher.write_text("#!/bin/sh\nexit 0\n")
        with self.assertRaisesRegex(RuntimeError, "nonstandard launcher"):
            self.runner.launcher(launcher, "selftest")


TERMINATING = (signal.SIGTERM, signal.SIGHUP)


def git(root, *args):
    done = subprocess.run(["git", "-C", str(root), *args], check=True,
                          capture_output=True, text=True,
                          env={**os.environ, "GIT_CONFIG_GLOBAL": "/dev/null",
                               "GIT_CONFIG_NOSYSTEM": "1",
                               "GIT_AUTHOR_NAME": "t",
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


@unittest.skipUnless(SHM.is_dir(), NO_SHM)
class FakeRepo(unittest.TestCase):
    """Tiny repository standing in for the pins: MAIN <- CAND, CONS, OTHER."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="task25-plan-",
                                                dir=SHM)
        self.base = Path(self.temp.name)
        self.repo = self.base / "repo"
        self.repo.mkdir()
        git(self.repo, "init", "-q", "-b", "main")
        scripts = {"src/auto/rules/n%dScript.sml" % i: "val x = [a = %d];\n"
                   % i for i in range(4)}
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
        self.config = self.repo / "sigobj/Systeml.sml"  # untracked, as real
        self.set_configured_alias("/dev/shm/t32-s3-derived")
        self.patch = self.base / "consumer.patch"
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

    def set_configured_alias(self, alias):
        self.config.parent.mkdir(exist_ok=True)
        self.config.write_text('val HOLDIR = "%s"\n' % alias)

    def args(self, **over):
        values = dict(consumer_patch=self.patch, patch_sha256=None,
                      consumer_revision=self.consumer,
                      simplifier_revision=self.main, alias=None,
                      scratch=None, jobs=None, skip_routine=False,
                      output=self.base / "out", existing_core=None,
                      existing_consumer=None)
        values.update(over)
        return argparse.Namespace(**values)

    def plan(self, **over):
        return task25.plan(self.args(**over), self.repo)

    def link(self, name, target):
        path = self.base / name
        path.symlink_to(target)
        return path


class Plan(FakeRepo):
    def test_defaults_are_the_pins(self):
        got = self.plan()
        self.assertEqual(got["simplifier"], self.main)
        self.assertFalse(got["patch_pin_overridden"])
        self.assertIsNone(got["scratch"])
        self.assertEqual(got["alias"], Path("/dev/shm/t32-s3-derived"))
        self.assertEqual(got["alias_config"], self.config)

    def test_descendant_resolved_to_full_hash(self):
        got = self.plan(simplifier_revision=self.cand[:12],
                        scratch=self.base / "s")
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

    def test_plan_returns_the_hashed_bytes(self):
        got = self.plan()
        self.assertEqual(task25.sha(got["patch_bytes"]),
                         got["patch_sha256"])
        self.assertEqual(got["patch_bytes"], self.patch.read_bytes())

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
        scratch = self.base / "s"
        self.assertEqual(self.plan(alias=Path("/dev/shm/a"),
                                   scratch=scratch)["alias"],
                         Path("/dev/shm/a"))
        for bad in ("rel/alias", "/dev/shm/a/../b", "/"):
            with self.assertRaisesRegex(RuntimeError, "--alias"):
                self.plan(alias=Path(bad), scratch=scratch)

    def test_scratch_required_unless_exact_task25(self):
        for over in (dict(simplifier_revision=self.cand),
                     dict(alias=Path("/dev/shm/a"))):
            with self.subTest(over=over):
                with self.assertRaisesRegex(RuntimeError,
                                            "--scratch is required"):
                    self.plan(**over)
        for over in (dict(jobs=4), dict(skip_routine=True)):
            with self.subTest(over=over):
                with self.assertRaisesRegex(RuntimeError,
                                            "--scratch is required"):
                    self.plan(**over)
        self.plan()  # the exact reproduction keeps the /tmp fallback

    def test_scratch_refusals(self):
        (self.repo / "ignored").mkdir()
        to_repo = self.link("to-ignored", self.repo / "ignored")
        to_tmp = self.link("to-tmp", "/tmp")
        for bad, why in ((Path("rel/scratch"), "absolute"),
                         (Path("/tmp/t32-s3-x"), "/tmp"),
                         (Path("/var/tmp/t32-s3-x"), "/tmp"),
                         (to_tmp / "t32-s3-x", "/tmp"),
                         (self.repo / "tracked/new", "inside or contain"),
                         (self.repo / "ignored/s", "inside or contain"),
                         (self.repo / "untracked-unignored",
                          "inside or contain"),
                         (self.repo, "inside or contain"),
                         (to_repo / "s", "inside or contain"),
                         (self.base, "inside or contain"),
                         (self.base / "no-parent/s", "parent directory")):
            with self.subTest(bad=str(bad)):
                with self.assertRaisesRegex(RuntimeError, why):
                    self.plan(scratch=bad, simplifier_revision=self.cand)

    def test_scratch_existing_refused(self):
        (self.base / "there").mkdir()
        with self.assertRaisesRegex(RuntimeError, "already exists"):
            self.plan(scratch=self.base / "there")

    def test_scratch_outside_checkout_accepted_and_resolved(self):
        real_base = Path(os.path.realpath(self.base))
        got = self.plan(scratch=self.link("ok", real_base) / "s")
        self.assertEqual(got["scratch"], real_base / "s")

    def test_alias_overlaps_refused(self):
        core, consumer = self.base / "core", self.base / "consumer"
        core.mkdir()
        consumer.mkdir()
        scratch = self.base / "s"
        self.link("alink", scratch)
        cases = [(scratch, {}), (scratch / "in", {}), (self.base, {}),
                 (SHM, {}), (self.base / "alink", {}),
                 (self.base / "out", {}), (self.base / "out/x", {}),
                 (core, dict(existing_core=core, existing_consumer=consumer)),
                 (core / "x", dict(existing_core=core,
                                   existing_consumer=consumer)),
                 (consumer, dict(existing_core=core,
                                 existing_consumer=consumer)),
                 (self.repo / "x", {}), (self.repo, {})]
        for alias, extra in cases:
            with self.subTest(alias=str(alias)):
                with self.assertRaisesRegex(RuntimeError, "alias overlaps|"
                                            "configured alias"):
                    self.plan(alias=alias, scratch=scratch, **extra)

    def test_alias_covering_tmp_refused_in_default_mode(self):
        self.set_configured_alias("/var/tmp")
        with self.assertRaisesRegex(RuntimeError, "alias overlaps"):
            self.plan()

    def test_unsafe_alias_parent_refused(self):
        with self.assertRaisesRegex(RuntimeError, "unsafe configured alias"):
            self.plan(alias=Path("/t32-s3-top"), scratch=self.base / "s")

    def test_output_rule_in_default_mode(self):
        self.assertEqual(self.plan(output=self.repo / "ignored/o")["output"],
                         self.repo / "ignored/o")
        for bad, why in ((self.repo / "tracked/o", "tracked tree"),
                         (self.repo / "untracked-unignored", "not ignored"),
                         (self.repo.parent, "contains caller")):
            with self.subTest(bad=str(bad)):
                with self.assertRaisesRegex(RuntimeError, why):
                    self.plan(output=bad)

    def test_output_symlink_into_tracked_refused(self):
        with self.assertRaisesRegex(RuntimeError, "tracked tree"):
            self.plan(output=self.link("o", self.repo / "tracked") / "o")

    def test_output_existing_or_in_scratch_refused(self):
        (self.base / "out").mkdir()
        with self.assertRaisesRegex(RuntimeError, "output already exists"):
            self.plan()
        with self.assertRaisesRegex(RuntimeError, "output overlaps scratch"):
            self.plan(output=self.base / "s/out", scratch=self.base / "s")

    def test_reuse_needs_both_trees(self):
        with self.assertRaisesRegex(RuntimeError, "reuse requires both"):
            self.plan(existing_core=self.base)

    def test_alias_mismatch_refused(self):
        core = self.base / "core"
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
    def test_mount_ops_in_exact_order(self):
        scratch = Path("/dev/shm/t32-consumer")
        alias = Path("/dev/shm/t32-alias")
        runner = task25.Runner(self.repo, self.base / "out", scratch, alias,
                               scratch / "core", scratch / "consumer")
        runner.git_common = self.repo / ".git"
        cmd = runner.sandbox(["true"])
        ops = cmd[:cmd.index("--setenv")]
        self.assertEqual(ops, [
            "bwrap", "--die-with-parent", "--clearenv", "--unshare-pid",
            "--unshare-net", "--ro-bind", "/", "/", "--dev", "/dev",
            "--proc", "/proc", "--tmpfs", "/tmp",
            "--tmpfs", "/dev/shm",
            "--bind", str(scratch), str(scratch),
            "--bind", str(scratch / "core"), str(alias),
            "--ro-bind", str(self.repo), str(self.repo),
            "--ro-bind", str(self.repo / ".git"), str(self.repo / ".git")])


class PrepareOnly(FakeRepo):
    """Whole driver, prepare-only: no build process, real git and patch."""

    runs = 0

    def scratch_path(self):
        return SHM / ("t32-s3-unit-%d-%s" % (os.getpid(), self.id()[-24:]))

    def run_main(self, *extra, revision=None, scratch=None,
                 expect_exit=False):
        PrepareOnly.runs += 1
        self.out = self.base / ("out%d" % PrepareOnly.runs)
        scratch = scratch or self.scratch_path()
        self.addCleanup(lambda: scratch.exists() and shutil.rmtree(scratch))
        argv = ["driver", "--consumer-patch", str(self.patch),
                "--output", str(self.out), "--prepare-only",
                "--simplifier-revision", revision or self.cand,
                "--alias", "/dev/shm/t32-s3-unit-alias",
                "--scratch", str(scratch), *extra]
        saved = (sys.argv, task25.__file__)
        sys.argv = argv
        fake = self.repo / "a/b/c/d/driver.py"
        fake.parent.mkdir(parents=True, exist_ok=True)
        fake.write_text("#\n")
        task25.__file__ = str(fake)
        self.exit = None
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                task25.main()
        except SystemExit as exc:
            if not expect_exit:
                raise
            self.exit = exc
        finally:
            sys.argv, task25.__file__ = saved
        manifest = json.loads((self.out / "manifest.json").read_text())
        if self.exit is None:  # the exit status must follow the disk manifest
            self.assertTrue(manifest["success"])
        else:
            self.assertFalse(manifest["success"])
            self.assertEqual(str(self.exit), "; ".join(
                manifest[k] for k in ("failure", "cleanup_failure")
                if k in manifest))
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

    def test_logs_are_compressed_and_hashed(self):
        m, _ = self.run_main()
        self.assertEqual(list(self.out.glob("*.log")), [])
        self.assertTrue(m["runs"])
        for record in m["runs"]:
            packed = self.out / record["log"]
            self.assertTrue(record["log"].endswith(".log.gz"))
            self.assertEqual(record["output"]["sha256"],
                             task25.sha(gzip.decompress(
                                 packed.read_bytes())))
            self.assertEqual(record["log_gz"], task25.fingerprint(packed))

    def test_patch_read_once_and_written_as_hashed(self):
        reads = []
        original = task25.Path.read_bytes

        def counting(path):
            reads.append(str(path))
            return original(path)
        with mock.patch.object(task25.Path, "read_bytes", counting):
            m, _ = self.run_main()
        self.assertEqual(reads.count(str(self.patch)), 1)
        written = (self.out / "consumer.patch").read_bytes()
        self.assertEqual(task25.sha(written), m["patch_sha256"])

    def test_scratch_run_holds_the_serial_lock(self):
        events = []

        @contextlib.contextmanager
        def lock(repo):
            events.append(("take", Path(repo).resolve(),
                           self.scratch_path().exists()))
            try:
                yield
            finally:
                events.append(("release", self.scratch_path().exists()))
        with mock.patch.object(task25, "serial_lock", lock):
            self.run_main()
        # Taken on the caller checkout before the scratch exists, released
        # only after it was removed.
        self.assertEqual(events, [("take", self.repo.resolve(), False),
                                  ("release", False)])

    def test_busy_serial_lock_refuses_and_creates_nothing(self):
        with task25.serial_lock(self.repo):
            with self.assertRaisesRegex(SystemExit, "refusing to run.*busy"):
                self.run_main()
        self.assertFalse(self.out.exists())
        self.assertFalse(self.scratch_path().exists())

    def test_no_scratch_does_not_take_the_lock(self):
        taken = []
        with mock.patch.object(task25, "serial_lock",
                               lambda repo: taken.append(repo)):
            with task25.run_lock(self.args(scratch=None), self.repo):
                pass
        self.assertEqual(taken, [])

    def test_wrong_revision_leaves_no_output(self):
        with self.assertRaisesRegex(RuntimeError, "does not descend"):
            self.run_main(revision=self.other)
        self.assertFalse(self.out.exists())

    def test_in_repo_scratch_refused_nothing_created(self):
        (self.repo / "ignored").mkdir()
        through = self.link("through", self.repo / "ignored")
        for scratch in (self.repo / "ignored/s", through / "s"):
            with self.subTest(scratch=str(scratch)):
                with self.assertRaisesRegex(RuntimeError,
                                            "inside or contain"):
                    self.run_main(scratch=scratch)
                self.assertFalse(self.out.exists())
                self.assertFalse((self.repo / "ignored/s").exists())

    def test_git_ceiling_passed_to_patch_commands(self):
        seen, popen = [], subprocess.Popen

        def spy(command, *a, **kw):
            seen.append((list(command), kw.get("cwd"), kw.get("env")))
            return popen(command, *a, **kw)
        with mock.patch.object(task25.subprocess, "Popen", spy):
            _, scratch = self.run_main()
        ceiling = str(Path(os.path.realpath(scratch)))
        applies = [(cwd, env) for command, cwd, env in seen
                   if command[:2] == ["git", "apply"]]
        self.assertEqual(len(applies), 3)
        for cwd, env in applies:
            self.assertTrue(Path(cwd).is_relative_to(scratch))
            self.assertEqual(env["GIT_CEILING_DIRECTORIES"], ceiling)

    def test_scratch_inside_another_repository(self):
        outer = self.base / "outer"
        outer.mkdir()
        git(outer, "init", "-q")
        m, scratch = self.run_main(scratch=outer / "s")
        self.assertTrue(m["success"])
        self.assertFalse(scratch.exists())
        inventory = json.loads(gzip.decompress(
            (self.out / m["consumer_canonical"]["file"]).read_bytes()))
        self.assertEqual(
            inventory["src/auto/rules/Holmakefile"]["sha256"],
            task25.sha(b"\n# patched\n"))

    def test_ignored_signal_stays_ignored(self):
        seen, archive = [], task25.Runner.archive

        def spy(runner, *a, **kw):
            seen.append((signal.getsignal(signal.SIGHUP),
                         signal.getsignal(signal.SIGTERM)))
            return archive(runner, *a, **kw)
        previous = signal.signal(signal.SIGHUP, signal.SIG_IGN)
        try:
            with mock.patch.object(task25.Runner, "archive", spy):
                m, _ = self.run_main()
            after = signal.getsignal(signal.SIGHUP)
        finally:
            signal.signal(signal.SIGHUP, previous)
        self.assertTrue(m["success"])
        self.assertEqual(seen[0][0], signal.SIG_IGN)
        self.assertTrue(callable(seen[0][1]))
        self.assertEqual(after, signal.SIG_IGN)

    def test_signal_during_cleanup_still_cleans_and_records(self):
        rmtree = shutil.rmtree

        def signalling(path, *a, **kw):
            os.kill(os.getpid(), signal.SIGTERM)
            return rmtree(path, *a, **kw)
        with mock.patch.object(task25.shutil, "rmtree", signalling):
            m, scratch = self.run_main(expect_exit=True)
        self.assertFalse(scratch.exists())
        self.assertTrue(m["task_scratch_removed"])
        self.assertFalse(m["success"])
        self.assertIn("terminated by SIGTERM", m["failure"])

    def test_ignored_signal_during_cleanup_is_not_a_failure(self):
        rmtree = shutil.rmtree

        def signalling(path, *a, **kw):
            os.kill(os.getpid(), signal.SIGHUP)
            return rmtree(path, *a, **kw)
        previous = signal.signal(signal.SIGHUP, signal.SIG_IGN)
        try:
            with mock.patch.object(task25.shutil, "rmtree", signalling):
                m, scratch = self.run_main()
        finally:
            signal.signal(signal.SIGHUP, previous)
        self.assertTrue(m["success"])
        self.assertNotIn("failure", m)
        self.assertIsNone(self.exit)

    def test_signal_after_final_write_is_ignored(self):
        finish = task25.finish

        def late(*a, **kw):
            finish(*a, **kw)
            os.kill(os.getpid(), signal.SIGTERM)
            os.kill(os.getpid(), signal.SIGINT)
        with mock.patch.object(task25, "finish", late):
            m, scratch = self.run_main()  # run_main checks exit == manifest
        self.assertTrue(m["success"])
        self.assertIsNone(self.exit)
        self.assertFalse(scratch.exists())

    def test_signal_at_finish_entry_is_a_recorded_failure(self):
        finish = task25.finish

        def early(*a, **kw):
            self.assertEqual(task25.STATE.mode, task25.DEFER)
            os.kill(os.getpid(), signal.SIGTERM)
            finish(*a, **kw)
        with mock.patch.object(task25, "finish", early):
            m, scratch = self.run_main(expect_exit=True)
        self.assertIn("terminated by SIGTERM", m["failure"])
        self.assertFalse(scratch.exists())
        self.assertTrue(m["task_scratch_removed"])

    def test_signal_raising_during_defer_still_finishes(self):
        def defer(state):
            os.kill(os.getpid(), signal.SIGTERM)
            time.sleep(5)
        with mock.patch.object(task25.SignalState, "defer", defer):
            m, scratch = self.run_main(expect_exit=True)
        self.assertIn("terminated by SIGTERM", m["failure"])
        self.assertFalse(scratch.exists())
        self.assertTrue(m["task_scratch_removed"])

    def test_signal_burst_raises_once(self):
        def archive(runner, *a, **kw):
            os.kill(os.getpid(), signal.SIGTERM)
            try:
                time.sleep(5)
            finally:
                os.kill(os.getpid(), signal.SIGHUP)  # during unwinding
                time.sleep(0.05)
        with mock.patch.object(task25.Runner, "archive", archive):
            m, scratch = self.run_main(expect_exit=True)
        self.assertIn("terminated by SIGTERM", m["failure"])
        self.assertFalse(scratch.exists())

    def test_signal_during_create_records_path_and_cleans(self):
        mkdir = task25.mkdir_scratch

        def signalling(path):
            os.kill(os.getpid(), signal.SIGTERM)
            return mkdir(path)
        with mock.patch.object(task25, "mkdir_scratch", signalling):
            m, scratch = self.run_main(expect_exit=True)
        self.assertIn("terminated by SIGTERM", m["failure"])
        self.assertFalse(scratch.exists())
        self.assertTrue(m["task_scratch_removed"])

    def test_keyboard_interrupt_exits_with_manifest_message(self):
        def archive(runner, *a, **kw):
            os.kill(os.getpid(), signal.SIGINT)
            time.sleep(5)
        with mock.patch.object(task25.Runner, "archive", archive):
            m, scratch = self.run_main(expect_exit=True)
        self.assertIn("KeyboardInterrupt", m["failure"])
        self.assertFalse(scratch.exists())

    def test_cleanup_failure_keeps_original_failure(self):
        self.patch.write_text(self.patch.read_text().replace(
            "@@ -1 +1,2 @@\n \n", "@@ -1 +1,2 @@\n x\n"))
        digest = task25.sha(self.patch.read_bytes())

        def broken(path, *a, **kw):
            raise OSError("nope")
        with mock.patch.object(task25.shutil, "rmtree", broken):
            m, _ = self.run_main("--patch-sha256", digest, expect_exit=True)
        self.assertIn("command failed: patch-check", m["failure"])
        self.assertNotIn("cleanup", m["failure"])
        self.assertIn("nope", m["cleanup_failure"])
        self.assertIn("command failed", str(self.exit))
        self.assertIn("nope", str(self.exit))
        self.assertFalse(m["task_scratch_removed"])

    def test_terminating_signal_cleans_scratch(self):
        for number in TERMINATING:
            with self.subTest(signal=number.name):
                previous = signal.getsignal(number)
                scratch = self.scratch_path()
                seen = []

                def archive(runner, revision, target, paths=()):
                    seen.append(scratch.is_dir())
                    os.kill(os.getpid(), number)
                    time.sleep(5)
                with mock.patch.object(task25.Runner, "archive", archive):
                    m, _ = self.run_main(expect_exit=True)
                self.assertEqual(seen, [True])
                self.assertIn("terminated by " + number.name, m["failure"])
                self.assertFalse(m["success"])
                self.assertTrue(m["task_scratch_removed"])
                self.assertFalse(scratch.exists())
                self.assertIsNotNone(self.exit)
                self.assertEqual(signal.getsignal(number), previous)

    def test_failure_after_scratch_exists_cleans_and_reports(self):
        self.patch.write_text(self.patch.read_text().replace(
            "@@ -1 +1,2 @@\n \n", "@@ -1 +1,2 @@\n x\n"))
        digest = task25.sha(self.patch.read_bytes())
        m, scratch = self.run_main("--patch-sha256", digest,
                                   expect_exit=True)
        self.assertFalse(m["success"])
        self.assertIn("command failed: patch-check", m["failure"])
        self.assertTrue(m["task_scratch_removed"])
        self.assertFalse(scratch.exists())
        self.assertIn("command failed", str(self.exit))

    def test_runner_construction_failure_cleans_and_reports(self):
        with mock.patch.object(task25, "Runner",
                               side_effect=RuntimeError("boom")):
            m, scratch = self.run_main(expect_exit=True)
        self.assertIn("boom", m["failure"])
        self.assertFalse(m["success"])
        self.assertFalse(scratch.exists())
        self.assertTrue(m["task_scratch_removed"])


if __name__ == "__main__":
    unittest.main(verbosity=2)
