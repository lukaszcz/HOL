"""The TASK37 re-targeting of the TASK32 and TASK33 drivers: the compiled
reference and the declaration are parameters whose defaults are the
TASK32/TASK33 ones, and the dispositions name their candidate."""
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
import task33_offline as offline
import task33_storage as storage


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


if __name__ == "__main__":
    unittest.main()
