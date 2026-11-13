"""The TASK37 re-targeting of the TASK32 and TASK33 drivers: the compiled
reference and the declaration are parameters whose defaults are the
TASK32/TASK33 ones, and the dispositions name their candidate."""
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import acceptance as a
import task32_downstream as dw
import task32_snapshots as snap
import task33_dispose as dispose
import task33_offline as offline
import task33_storage as storage
import task37_cases as cases37


def git(repo, *argv):
    return subprocess.run(
        ["git", "-C", str(repo), "-c", "user.name=t", "-c",
         "user.email=t@t", *argv], stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE, check=True).stdout.decode().strip()


class CompiledRef(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)
        self.repo = Path(self.dir.name)
        git(self.repo, "init", "-q")
        (self.repo / "src/boss").mkdir(parents=True)
        (self.repo / "src/boss/c.sml").write_text("0\n")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "one")
        self.one = git(self.repo, "rev-parse", "HEAD")
        (self.repo / "src/boss/c.sml").write_text("1\n")
        git(self.repo, "commit", "-q", "-a", "-m", "two")
        self.two = git(self.repo, "rev-parse", "HEAD")
        self.sides = dict(base=dict(pin=a.BASE), cand=dict(pin=self.two))

    def test_the_default_is_c31_and_a_ref_overrides_it(self):
        self.assertEqual(dw.COMPILED_REF, snap.C31)
        with mock.patch.object(dw, "COMPILED_REF", self.one):
            with self.assertRaisesRegex(dw.Refusal, "differ from"):
                dw.check_candidate(self.repo, self.sides)
            self.assertEqual(
                dw.check_candidate(self.repo, self.sides, self.two),
                self.two)

    def test_an_unresolvable_ref_is_refused(self):
        with self.assertRaisesRegex(dw.Refusal, "cannot resolve"):
            dw.check_candidate(self.repo, self.sides, "f" * 40)

    def test_the_verify_command_names_the_ref(self):
        sides = dict(base=dict(pin="1" * 40), cand=dict(pin="2" * 40))
        argv = dw.default_verify(self.repo, "m.json", sides)
        self.assertEqual(argv[argv.index("--compiled-ref") + 1], snap.C31)
        argv = dw.default_verify(self.repo, "m.json", sides, self.two)
        self.assertEqual(argv[argv.index("--compiled-ref") + 1], self.two)

    def test_the_snapshot_builder_takes_both_spellings(self):
        seen = []

        def fake(manifest, base_pin, cand_pin, c31=None, **kw):
            seen.append(c31)
            return dict(status="pass")
        manifest = Path(self.dir.name) / "m.json"
        manifest.write_text('{"schema": "x"}')
        for flag in ("--c31", "--compiled-ref"):
            argv = ["verify", "--repo", str(self.repo), "--manifest",
                    str(manifest), "--base-pin", "1" * 40, "--cand-pin",
                    "2" * 40, flag, "3" * 40]
            with mock.patch.object(snap, "verify", fake), \
                    mock.patch.object(snap.a, "serial_lock") as lock:
                lock.return_value.__enter__.return_value = []
                self.assertEqual(snap.main(argv), 0)
        self.assertEqual(seen, ["3" * 40, "3" * 40])


class StorageOptions(unittest.TestCase):
    def test_every_stage_command_takes_the_revision_options(self):
        parser = storage.build_parser()
        common = ["--repo", "r", "--base-root", "b", "--cand-root", "c",
                  "--manifest", "m", "--declared", "d.json",
                  "--compiled-ref", "abc"]
        args = parser.parse_args(["smoke", "--output", "o"] + common)
        self.assertEqual((args.declared, args.compiled_ref),
                         (Path("d.json"), "abc"))
        args = parser.parse_args(["replay", "x", "--declared", "d.json"])
        self.assertEqual(args.declared, Path("d.json"))
        args = parser.parse_args(
            ["dispose", "--stage", "s", "--timing-stage", "t", "--offline",
             "o", "--out", "out", "--declared", "d.json"])
        self.assertEqual(args.declared, Path("d.json"))
        args = parser.parse_args(
            ["dispose-snapshots", "--evidence", "e", "--manifest", "m",
             "--repo", "r", "--compiled-ref", "abc"])
        self.assertEqual(args.compiled_ref, "abc")
        args = parser.parse_args(["replay", "x"])
        self.assertIsNone(args.declared)

    def test_dispatch_selects_the_declaration_only_when_given(self):
        before = offline.DECLARED
        args = storage.build_parser().parse_args(
            ["replay", "x", "--declared", str(HERE / "task37_declared.json")])
        with mock.patch.object(storage.d, "require_ledger"), \
                mock.patch.object(storage, "replay_chain",
                                  side_effect=RuntimeError("stop")):
            try:
                with self.assertRaises(RuntimeError):
                    storage.dispatch(args)
                self.assertEqual(offline.DECLARED,
                                 HERE / "task37_declared.json")
            finally:
                offline.use_declared(before)
        self.assertEqual(offline.DECLARED, before)


class Histories(unittest.TestCase):
    def test_every_sealed_file_that_changed_keeps_its_old_seal(self):
        for name in ("task32_downstream.py", "task32_snapshots.py"):
            self.assertTrue(dw.TASK32_HISTORY[name], name)
            self.assertTrue(dw.TASK33_HISTORY[name], name)
        for name in ("task33_offline.py", "task33_storage.py",
                     "task33_rules.py", "task33_dispose.py"):
            self.assertTrue(dw.TASK33_HISTORY[name], name)
        for table in (dw.TASK32_HISTORY, dw.TASK33_HISTORY):
            for name, seals in table.items():
                for seal in seals:
                    self.assertEqual(len(seal["sha256"]), 64, name)
                    self.assertIsInstance(seal["bytes"], int)
                self.assertEqual(len({s["sha256"] for s in seals}),
                                 len(seals), name)

    def test_the_old_seals_are_not_the_current_ones(self):
        now = dw.code_seals()
        self.assertNotIn(now["task32_downstream.py"],
                         dw.TASK32_HISTORY["task32_downstream.py"])
        self.assertNotIn(
            offline.code_seals()["task33_offline.py"],
            dw.TASK33_HISTORY["task33_offline.py"])


class DeclaredPins(unittest.TestCase):
    """The declaration of a gate is the one of its pins (3a), of its
    offline reports (3b), and filled before a predeclaration (3c)."""
    TASK37 = HERE / "task37_declared.json"

    def selected(self, path):
        before = offline.use_declared(path)
        self.addCleanup(offline.use_declared, before)

    def test_the_stage_pins_must_be_the_declarations(self):
        declared = offline.load_declared()
        storage.check_declared(declared["base"], declared["cand"])
        with self.assertRaisesRegex(storage.d.Refusal, "for cand"):
            storage.check_declared(declared["base"], "f" * 40)
        with self.assertRaisesRegex(storage.d.Refusal, "for base"):
            storage.check_declared("f" * 40, declared["cand"])
        self.selected(self.TASK37)
        with self.assertRaisesRegex(storage.d.Refusal, "for cand"):
            storage.check_declared(declared["base"], declared["cand"])

    def test_the_task33_declaration_names_the_kept_records_pins(self):
        declared = offline.load_declared()
        self.assertEqual(declared["base"], a.BASE)
        self.assertEqual(declared["cand"],
                         "e436752631f54a563679bd184a64c3d4ed249c23")

    def test_a_stage_is_refused_before_anything_runs_on_other_pins(self):
        sides = dict(base=dict(pin=a.BASE), cand=dict(pin="a" * 40))
        args = mock.Mock()
        with mock.patch.object(storage.d, "pins_of",
                               return_value=(sides, {})), \
                mock.patch.object(storage.d, "run_stage") as stage:
            with self.assertRaisesRegex(storage.d.Refusal, "for cand"):
                storage.run(args, dict(mode="smoke"))
        stage.assert_not_called()

    def test_predeclare_refuses_a_placeholder_inside_the_refusal_path(self):
        self.selected(self.TASK37)
        declared = offline.load_declared()
        sides = dict(base=dict(pin=declared["base"]),
                     cand=dict(pin=declared["cand"]))
        for name in ("predeclare_run", "predeclare_followup"):
            with mock.patch.object(storage.d, "pins_of",
                                   return_value=(sides, {})):
                with self.assertRaisesRegex(storage.d.Refusal,
                                            "not ready.*pending"):
                    getattr(storage, name)(mock.Mock())
        with self.assertRaises(storage.d.Refusal):
            storage.declared_ready()
        self.selected(offline.DECLARED.parent / "task33_declared.json")
        storage.declared_ready()   # TASK33's own is valid

    def test_a_placeholder_decision_is_a_refusal_not_a_traceback(self):
        self.selected(self.TASK37)
        with self.assertRaisesRegex(storage.d.Refusal, "not measured"):
            storage.refusing(storage.rules.total_deltas,
                             offline.load_declared())

    def test_dispose_requires_the_reports_declaration(self):
        own = a.seal(offline.DECLARED)
        other = dict(own, sha256="0" * 64)
        with tempfile.TemporaryDirectory() as tmp:
            counts = Path(tmp) / "counts.json"
            counts.write_text(json.dumps(dict(offline={
                c: dict(seal="s-" + c) for c in dispose.OFFLINE})))

            def found(declared):
                return {c: (dict(inputs=dict(declared=declared)),
                            dict(seal="s-" + c))
                        for c in dispose.OFFLINE}
            with mock.patch.object(storage, "storage_counts_path",
                                   return_value=counts):
                dispose.check_offline_identity(found(own), mock.Mock())
                for bad in (other, None):
                    with self.assertRaisesRegex(
                            storage.d.Refusal, "another declaration"):
                        dispose.check_offline_identity(found(bad),
                                                       mock.Mock())


class ScratchAndConstants(unittest.TestCase):
    def test_the_compiled_ref_is_the_final_candidate_in_full(self):
        self.assertRegex(cases37.COMPILED_REF, "^[0-9a-f]{40}$")
        self.assertTrue(cases37.COMPILED_REF.startswith("7e202dfbaa"))

    def test_the_t_run_and_the_s_run_have_distinct_scratch(self):
        timing = Path(dw.TABLES["task33"].scratch)
        self.assertNotEqual(storage.STORAGE_SCRATCH, timing)
        self.assertEqual(timing, storage.SCRATCH_ROOT)
        self.assertEqual(storage.STORAGE_SCRATCH.parent,
                         storage.SCRATCH_ROOT)  # one disposal removes both
        args = storage.build_parser().parse_args(
            ["smoke", "--output", "o", "--repo", "r", "--base-root", "b",
             "--cand-root", "c", "--manifest", "m"])
        self.assertEqual(args.scratch, storage.STORAGE_SCRATCH)

    def test_a_root_removed_in_between_is_created_again(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / "root" / "run-x"
            real = Path.mkdir
            calls = []

            def racing(self, *a_, **k):
                calls.append(self)
                if len(calls) == 1:
                    raise FileNotFoundError(2, "root removed", str(self))
                return real(self, *a_, **k)
            with mock.patch.object(Path, "mkdir", racing):
                dw.make_scratch(target)
            self.assertTrue(target.is_dir())
            self.assertGreaterEqual(calls.count(target), 2)
            with self.assertRaises(FileExistsError):
                dw.make_scratch(target)  # a folder that exists is refused
            with mock.patch.object(Path, "mkdir",
                                   side_effect=FileNotFoundError):
                with self.assertRaisesRegex(dw.Refusal, "cannot create"):
                    dw.make_scratch(Path(tmp) / "never")


def evidence_root():
    """The directory of the kept TASK32/TASK33 evidence (outside git): the
    environment's TASK37_EVIDENCE, else the checkout's, else its origin's
    (a stream clone's origin is the main worktree)."""
    found = [os.environ.get("TASK37_EVIDENCE")]
    for argv in (["rev-parse", "--show-toplevel"],
                 ["remote", "get-url", "origin"]):
        done = subprocess.run(["git", "-C", str(HERE)] + argv,
                              stdin=subprocess.DEVNULL,
                              stdout=subprocess.PIPE,
                              stderr=subprocess.DEVNULL)
        if done.returncode == 0:
            found.append(done.stdout.decode().strip() +
                         "/.agent-files/evidence")
    for path in found:
        if path and (Path(path) / "task33/r4/disposition.json").is_file() \
                and (Path(path) / "task32/first/downstream.json").is_file():
            return Path(path)
    return None


# the head the kept TASK33 records were replayed at (r4/runs/steps-replay)
KEPT_HEAD = "3bc16467f3"


@unittest.skipUnless(evidence_root(), "the kept TASK32/TASK33 evidence "
                     "(.agent-files/evidence, outside git) is not present")
class KeptRecordsReplay(unittest.TestCase):
    """The kept TASK32 and TASK33 records still replay with the current
    drivers (the histories name the seals they were made by). The replays
    are read-only; the repository they need is a throwaway one at the
    head the records were replayed at, borrowing this checkout's objects
    (the drivers refuse a HEAD that changes the compiled sources)."""
    @classmethod
    def setUpClass(cls):
        cls.dir = tempfile.TemporaryDirectory()
        cls.repo = Path(cls.dir.name) / "repo"
        objects = subprocess.run(
            ["git", "-C", str(HERE), "rev-parse", "--path-format=absolute",
             "--git-path", "objects"], stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, check=True).stdout.decode().strip()
        git(cls.repo.parent, "init", "-q", str(cls.repo))
        (cls.repo / ".git/objects/info/alternates").write_text(
            objects + "\n")
        try:
            git(cls.repo, "update-ref", "HEAD", KEPT_HEAD)
            git(cls.repo, "cat-file", "-e", KEPT_HEAD + "^{commit}")
        except subprocess.CalledProcessError:
            cls.dir.cleanup()
            raise unittest.SkipTest("%s is not in this repository" %
                                    KEPT_HEAD)
        cls.perf = "src/simp/tests/performance/"
        git(cls.repo, "checkout", "-q", "HEAD", "--", *[
            cls.perf + n for n in ("task32_counts.json",
                                   "task33_counts.json",
                                   "task33_storage_counts.json")])
        cls.ev = evidence_root()

    @classmethod
    def tearDownClass(cls):
        cls.dir.cleanup()

    def cli(self, script, *argv):
        env = dict(os.environ, TMPDIR=self.dir.name)
        return subprocess.run(
            [sys.executable, "-B", str(HERE / script)] + list(argv),
            cwd=str(HERE), env=env, stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def test_the_task32_first_stage_replays(self):
        done = self.cli(
            "task32_downstream.py", "replay", str(self.ev / "task32/first"),
            "--repo", str(self.repo), "--ledger",
            str(self.ev / "task32/attempts.jsonl"), "--counts",
            str(self.repo / self.perf / "task32_counts.json"))
        out = done.stdout.decode()
        self.assertEqual(done.returncode, 0, out)
        info = json.loads(out.strip().splitlines()[-1])
        self.assertEqual((info["exit"], info["mode"], info["replayed"]),
                         ("pass", "first", 4240))

    def test_the_task33_r4_records_dispose_as_they_did(self):
        r4 = self.ev / "task33/r4"
        out = Path(self.dir.name) / "disposition.json"
        done = self.cli(
            "task33_storage.py", "dispose", "--stage", str(r4 / "s-run"),
            "--stage", str(r4 / "s-audit"), "--timing-stage",
            str(r4 / "t-run"), "--offline", str(r4 / "offline/audit.json"),
            "--offline", str(r4 / "offline/harvest/harvest.json"),
            "--offline", str(r4 / "offline/archive.json"), "--out",
            str(out), "--repo", str(self.repo), "--ledger",
            str(self.ev / "task33/attempts.jsonl"), "--manifest",
            str(self.ev / "task32/snapshots.json"), "--timing-counts",
            str(self.repo / self.perf / "task33_counts.json"),
            "--storage-counts",
            str(self.repo / self.perf / "task33_storage_counts.json"))
        self.assertEqual(done.returncode, 0, done.stdout.decode())
        new = json.loads(out.read_text())
        kept = json.loads((r4 / "disposition.json").read_text())
        self.assertEqual(new["status"], kept["status"])
        self.assertEqual(new["counts"], kept["counts"])
        self.assertEqual(new["decisions"], kept["decisions"])
        self.assertEqual(new["candidate"],
                         "e436752631f54a563679bd184a64c3d4ed249c23")

    def test_a_record_does_not_replay_under_another_declaration(self):
        r4 = self.ev / "task33/r4"
        done = self.cli(
            "task33_storage.py", "replay", str(r4 / "s-smoke"),
            "--repo", str(self.repo), "--ledger",
            str(self.ev / "task33/attempts.jsonl"), "--manifest",
            str(self.ev / "task32/snapshots.json"), "--timing-counts",
            str(self.repo / self.perf / "task33_counts.json"),
            "--declared", str(HERE / "task37_declared.json"))
        self.assertEqual(done.returncode, 3, done.stdout.decode())
        self.assertIn("declaration", done.stdout.decode())


if __name__ == "__main__":
    unittest.main()
