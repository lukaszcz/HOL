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
import task37_gates as gates


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

    def test_dispatch_selects_the_declaration_for_the_command_only(self):
        before = offline.DECLARED
        args = storage.build_parser().parse_args(
            ["replay", "x", "--declared", str(HERE / "task37_declared.json")])
        seen = []

        def stop(args):
            seen.append(offline.DECLARED)
            raise RuntimeError("stop")
        with mock.patch.object(storage, "run_command", stop):
            with self.assertRaises(RuntimeError):
                storage.dispatch(args)
        self.assertEqual(seen, [HERE / "task37_declared.json"])
        self.assertEqual(offline.DECLARED, before)  # not leaked
        args = storage.build_parser().parse_args(["replay", "x"])
        with mock.patch.object(storage, "run_command", stop):
            with self.assertRaises(RuntimeError):
                storage.dispatch(args)
        self.assertEqual(seen[-1], before)  # only when given


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
            args = mock.Mock(repo=None)
            with mock.patch.object(storage, "storage_counts_path",
                                   return_value=counts), \
                    mock.patch.object(storage, "check_archive_binding"):
                dispose.check_offline_identity(found(own), args)
                for bad in (other, None):
                    with self.assertRaisesRegex(
                            storage.d.Refusal, "another declaration"):
                        dispose.check_offline_identity(found(bad), args)

    def test_dispose_binds_the_archive_report(self):
        own = a.seal(offline.DECLARED)
        with tempfile.TemporaryDirectory() as tmp:
            counts = Path(tmp) / "counts.json"
            counts.write_text(json.dumps(dict(offline={
                c: dict(seal="s-" + c) for c in dispose.OFFLINE})))
            found = {c: (dict(inputs=dict(declared=own)),
                         dict(seal="s-" + c)) for c in dispose.OFFLINE}
            with mock.patch.object(storage, "storage_counts_path",
                                   return_value=counts), \
                    mock.patch.object(
                        storage, "check_archive_binding",
                        side_effect=storage.d.Refusal("not bound")) as bound:
                with self.assertRaisesRegex(storage.d.Refusal, "not bound"):
                    dispose.check_offline_identity(found, mock.Mock(
                        repo="r"))
                bound.assert_called_once_with(found["archive"][0], "r")


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

    def test_the_task37_t_run_and_s_run_have_distinct_scratch(self):
        timing = Path(dw.TABLES["task37-t33"].scratch)
        with storage.using_storage_table("task37-t33"):
            self.assertEqual(timing, Path("/dev/shm/t37-t33"))
            self.assertEqual(timing, storage.SCRATCH_ROOT)
            self.assertEqual(storage.STORAGE_SCRATCH, timing / "storage")
            args = storage.build_parser().parse_args(
                ["smoke", "--output", "o", "--repo", "r", "--base-root",
                 "b", "--cand-root", "c", "--manifest", "m"])
            self.assertEqual(args.scratch, storage.STORAGE_SCRATCH)
            args = storage.build_parser().parse_args(
                ["dispose-snapshots", "--evidence", "e", "--manifest", "m",
                 "--repo", "r"])
            self.assertEqual(args.scratch_root, timing)
        self.assertEqual(storage.SCRATCH_ROOT, Path("/dev/shm/t33"))

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


TABLES = ("task32", "task33", "task37-t32", "task37-t33")


class Tables37(unittest.TestCase):
    """Design decision 22: TASK37's own TASK32 and TASK33 tables."""

    def test_every_table_has_its_own_counts_seeds_ledger_journals_scratch(
            self):
        for field in ("counts", "followup_counts", "seed", "ledger_table",
                      "ledger_dir", "journals", "scratch"):
            values = [str(getattr(dw.TABLES[n], field)) for n in TABLES]
            self.assertEqual(len(set(values)), len(TABLES), (field, values))
        self.assertEqual(sorted(dw.TABLES), sorted(TABLES))

    def test_the_task37_tables_are_named_in_parallel_to_the_c32_ones(self):
        t32, t33 = dw.TABLES["task37-t32"], dw.TABLES["task37-t33"]
        self.assertEqual(
            (t32.counts.name, t32.followup_counts.name, t32.seed,
             t32.ledger_table, t32.ledger_dir, t32.journals, t32.scratch),
            ("task37_t32_counts.json", "task37_t32_followup_counts.json",
             "task37-t32-1", "task37-t32-downstream", "task37-t32",
             ".agent-files/scratch/task37-t32", "/dev/shm/t37-t32"))
        self.assertEqual(
            (t33.counts.name, t33.followup_counts.name, t33.seed,
             t33.ledger_table, t33.ledger_dir, t33.journals, t33.scratch),
            ("task37_t33_counts.json", "task37_t33_followup_counts.json",
             "task37-t33-1", "task37-t33-loading", "task37-t33",
             ".agent-files/scratch/task37-t33", "/dev/shm/t37-t33"))

    def test_a_task37_table_is_its_parent_with_no_history(self):
        for new, parent in (("task37-t32", "task32"),
                            ("task37-t33", "task33")):
            one, two = dw.TABLES[new], dw.TABLES[parent]
            for field in ("cases", "code", "min_unit_cpu", "unit_floor",
                          "r_cap", "sample_cpu", "claims", "cross_side",
                          "env_prefix", "probe_sources", "probe_digest"):
                self.assertEqual(getattr(one, field), getattr(two, field),
                                 (new, field))
            self.assertEqual(one.history, {})
            self.assertTrue(two.history or parent == "task32")

    def test_the_c32_tables_are_unchanged(self):
        t32, t33 = dw.TABLES["task32"], dw.TABLES["task33"]
        self.assertEqual(
            (t32.counts.name, t32.followup_counts.name, t32.seed,
             t32.ledger_table, t32.journals, t32.scratch),
            ("task32_counts.json", "task32_followup_counts.json",
             "task32-1", "task32-downstream",
             ".agent-files/scratch/task32", "/dev/shm/t32"))
        self.assertEqual(
            (t33.counts.name, t33.followup_counts.name, t33.seed,
             t33.ledger_table, t33.journals, t33.scratch),
            ("task33_counts.json", "task33_followup_counts.json",
             "task33-1", "task33-loading",
             ".agent-files/scratch/task33", "/dev/shm/t33"))
        for table in (t32, t33):
            self.assertIsNone(table.compiled_ref)
            self.assertIsNone(table.declared)
        self.assertEqual(dw.DEFAULT_TABLE, "task32")
        self.assertEqual(
            (storage.DEFAULT_TABLE, storage.ACTIVE_STORAGE, storage.TABLE,
             storage.LEDGER_TABLE, storage.SEED, storage.SCRATCH_ROOT,
             storage.STORAGE_COUNTS.name, storage.FOLLOWUP_COUNTS.name),
            ("task33", "task33", "task33", "task33-storage", "task33-s4",
             Path("/dev/shm/t33"), "task33_storage_counts.json",
             "task33_storage_followup_counts.json"))

    def test_the_timing_driver_holds_its_own_literal_of_the_final_ref(self):
        # so that the C32 replays do not import the TASK37 modules
        self.assertEqual(dw.TASK37_COMPILED_REF, cases37.COMPILED_REF)
        self.assertEqual(dw.TABLES["task37-t32"].compiled_ref,
                         dw.TASK37_COMPILED_REF)
        code = (HERE / "task32_downstream.py").read_text()
        self.assertNotIn("import task37", code)

    def test_the_storage_scratch_roots_are_the_tables_scratch(self):
        for name, table in storage.STORAGE_TABLES.items():
            self.assertEqual(table.scratch_root,
                             Path(dw.TABLES[name].scratch), name)

    def test_the_task37_tables_fix_their_revision_and_declaration(self):
        self.assertEqual(dw.TABLES["task37-t32"].compiled_ref,
                         cases37.COMPILED_REF)
        self.assertEqual(dw.TABLES["task37-t33"].compiled_ref,
                         cases37.COMPILED_REF)
        self.assertEqual(dw.TABLES["task37-t33"].declared,
                         HERE / "task37_declared.json")
        self.assertIsNone(dw.TABLES["task37-t32"].declared)

    def test_the_storage_tables_are_distinct_and_named_as_the_timing_ones(
            self):
        tables = list(storage.STORAGE_TABLES.values())
        self.assertEqual(sorted(storage.STORAGE_TABLES),
                         ["task33", "task37-t33"])
        for field in ("ledger_table", "storage_counts", "followup_counts",
                      "seed", "scratch_root"):
            values = [str(getattr(t, field)) for t in tables]
            self.assertEqual(len(set(values)), len(tables), field)
        for name in storage.STORAGE_TABLES:  # one name for both drivers
            self.assertIn(name, dw.TABLES)
        other = storage.STORAGE_TABLES["task37-t33"]
        timing = dw.TABLES["task37-t33"]
        self.assertNotEqual(other.ledger_table, timing.ledger_table)
        self.assertNotEqual(str(other.storage_counts), str(timing.counts))
        self.assertEqual(
            (other.storage_counts.name, other.followup_counts.name,
             other.seed, other.ledger_table, other.scratch_root),
            ("task37_t33_storage_counts.json",
             "task37_t33_storage_followup_counts.json", "task37-t33-s4",
             "task37-t33-storage", Path("/dev/shm/t37-t33")))

    def test_selecting_a_storage_table_sets_every_constant_and_restores(
            self):
        with storage.using_storage_table("task37-t33"):
            self.assertEqual(
                (storage.TABLE, storage.LEDGER_TABLE, storage.SEED,
                 storage.STORAGE_COUNTS.name, storage.FOLLOWUP_COUNTS.name,
                 storage.SCRATCH_ROOT, storage.STORAGE_SCRATCH),
                ("task37-t33", "task37-t33-storage", "task37-t33-s4",
                 "task37_t33_storage_counts.json",
                 "task37_t33_storage_followup_counts.json",
                 Path("/dev/shm/t37-t33"),
                 Path("/dev/shm/t37-t33/storage")))
            self.assertEqual(sorted(storage.SEEDS.values()), sorted(
                "task37-t33-s4-" + s for s in storage.STORAGE_STAGES))
        self.assertEqual(storage.SEED, "task33-s4")
        self.assertEqual(storage.SEEDS["smoke"], "task33-s4-smoke")
        with self.assertRaisesRegex(dw.Refusal, "unknown table"):
            storage.use_storage_table("task37")
        self.assertEqual(storage.ACTIVE_STORAGE, "task33")

    def test_the_table_option_selects_it_before_the_parser_is_built(self):
        try:
            self.assertEqual(storage.select_table(
                ["--table", "task37-t33", "replay", "x"]), "task37-t33")
            self.assertEqual(storage.LEDGER_TABLE, "task37-t33-storage")
            args = storage.build_parser().parse_args(
                ["--table", "task37-t33", "replay", "x"])
            self.assertEqual(args.table, "task37-t33")
            self.assertEqual(storage.select_table(["replay", "x"]),
                             "task33")
            self.assertEqual(storage.LEDGER_TABLE, "task33-storage")
            self.assertEqual(storage.build_parser().parse_args(
                ["replay", "x"]).table, "task33")
        finally:
            storage.use_storage_table("task33")

    def test_main_runs_the_storage_driver_under_the_table_named(self):
        seen = []

        def fake(argv, **kw):
            seen.append((kw["table"], storage.LEDGER_TABLE))
            return 0
        try:
            with mock.patch.object(dw, "main", fake):
                storage.main(["--table", "task37-t33", "replay", "x"])
                storage.main(["replay", "x"])
        finally:
            storage.use_storage_table("task33")
        self.assertEqual(seen, [("task37-t33", "task37-t33-storage"),
                                ("task33", "task33-storage")])

    def test_the_dispose_runs_the_timing_chain_under_the_selected_table(
            self):
        seen = []

        def stop(*a_, **k):
            seen.append(dw.ACTIVE.name)
            raise RuntimeError("stop")
        for name in ("task33", "task37-t33"):
            args = mock.Mock(relocated=[], offline=[])
            with storage.using_storage_table(name), \
                    mock.patch.object(dispose, "load_offline",
                                      return_value={}), \
                    mock.patch.object(dispose, "check_offline_identity"), \
                    mock.patch.object(dw, "replay_chain", stop):
                with self.assertRaises(RuntimeError):
                    dispose.dispose(args)
        self.assertEqual(seen, ["task33", "task37-t33"])


class FixedRevision(unittest.TestCase):
    """`--compiled-ref` and `--declared` on a table that fixes them."""
    def test_the_c32_tables_take_the_option_or_c31(self):
        for name in ("task32", "task33"):
            table = dw.TABLES[name]
            self.assertEqual(dw.resolve_ref(None, table), snap.C31)
            self.assertEqual(dw.resolve_ref("abc", table), "abc")

    def test_a_fixed_table_refuses_a_contradicting_ref(self):
        for name in ("task37-t32", "task37-t33"):
            table = dw.TABLES[name]
            fixed = cases37.COMPILED_REF
            self.assertEqual(dw.resolve_ref(None, table), fixed)
            self.assertEqual(dw.resolve_ref(fixed, table), fixed)
            self.assertEqual(dw.resolve_ref(fixed[:12], table), fixed)
            for bad in (snap.C31, "a" * 40, fixed[:6], fixed[:-1] + "0"):
                with self.assertRaisesRegex(dw.Refusal, "contradicts"):
                    dw.resolve_ref(bad, table)

    def test_the_active_table_decides_the_verification_and_the_candidate(
            self):
        sides = dict(base=dict(pin="1" * 40), cand=dict(pin="2" * 40))
        with dw.using_table("task37-t32"):
            argv = dw.default_verify("r", "m.json", sides)
            self.assertEqual(argv[argv.index("--compiled-ref") + 1],
                             cases37.COMPILED_REF)
            with self.assertRaisesRegex(dw.Refusal, "contradicts"):
                dw.default_verify("r", "m.json", sides, snap.C31)
            with self.assertRaisesRegex(dw.Refusal, "contradicts"):
                dw.check_candidate("r", dict(
                    base=dict(pin=a.BASE), cand=dict(pin="2" * 40)),
                    snap.C31)
        argv = dw.default_verify("r", "m.json", sides)
        self.assertEqual(argv[argv.index("--compiled-ref") + 1], snap.C31)

    def parse(self, *argv):
        return storage.build_parser().parse_args(list(argv))

    def stage(self, *extra):
        return self.parse("--table", "task37-t33", "smoke", "--output", "o",
                          "--repo", "r", "--base-root", "b", "--cand-root",
                          "c", "--manifest", "m", *extra)

    def test_a_contradicting_declared_or_ref_is_refused_before_anything(
            self):
        task37 = str(HERE / "task37_declared.json")
        with storage.using_storage_table("task37-t33"), \
                mock.patch.object(storage, "run_command") as run:
            for extra in (["--declared", str(HERE / "task33_declared.json")],
                          ["--compiled-ref", snap.C31]):
                with self.assertRaisesRegex(dw.Refusal, "contradicts"):
                    storage.dispatch(self.stage(*extra))
            run.assert_not_called()
            for extra in ([], ["--declared", task37],
                          ["--compiled-ref", cases37.COMPILED_REF],
                          ["--declared", str(HERE / ".." / "performance" /
                                             "task37_declared.json")]):
                run.reset_mock()
                storage.dispatch(self.stage(*extra))
                run.assert_called_once()

    def test_the_table_selects_its_declaration_when_none_is_given(self):
        seen = []
        before = offline.DECLARED
        with storage.using_storage_table("task37-t33"), \
                mock.patch.object(storage, "run_command",
                                  lambda args: seen.append(
                                      offline.DECLARED)):
            storage.dispatch(self.stage())
        self.assertEqual(seen, [HERE / "task37_declared.json"])
        self.assertEqual(offline.DECLARED, before)

    def test_the_c32_table_takes_any_declaration_and_ref(self):
        seen = []
        args = self.parse("smoke", "--output", "o", "--repo", "r",
                          "--base-root", "b", "--cand-root", "c",
                          "--manifest", "m", "--compiled-ref", "abc",
                          "--declared", str(HERE / "task37_declared.json"))
        with mock.patch.object(storage, "run_command",
                               lambda a_: seen.append(offline.DECLARED)):
            storage.dispatch(args)
        self.assertEqual(seen, [HERE / "task37_declared.json"])

    def test_the_table_of_the_arguments_must_be_the_selected_one(self):
        with self.assertRaisesRegex(dw.Refusal, "active table"):
            storage.dispatch(self.stage())


class CheckDeclaredEquivalence(unittest.TestCase):
    """A TASK37 candidate is the declared one or has its tree outside the
    performance area; the C32 table needs the exact one."""
    PERF = "src/simp/tests/performance/"

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)
        self.repo = Path(self.dir.name)
        git(self.repo, "init", "-q")
        (self.repo / "src/boss").mkdir(parents=True)
        (self.repo / self.PERF).mkdir(parents=True)
        (self.repo / "src/boss/c.sml").write_text("0\n")
        (self.repo / self.PERF / "p.py").write_text("0\n")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "declared")
        self.declared = git(self.repo, "rev-parse", "HEAD")
        (self.repo / self.PERF / "p.py").write_text("1\n")
        git(self.repo, "commit", "-q", "-a", "-m", "performance only")
        self.same = git(self.repo, "rev-parse", "HEAD")
        (self.repo / "src/boss/c.sml").write_text("1\n")
        git(self.repo, "commit", "-q", "-a", "-m", "source")
        self.other = git(self.repo, "rev-parse", "HEAD")
        patcher = mock.patch.object(
            offline, "load_declared", return_value=dict(
                base=a.BASE, cand=self.declared))
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_an_equivalent_candidate_is_accepted_by_the_task37_table(self):
        with storage.using_storage_table("task37-t33"):
            storage.check_declared(a.BASE, self.declared, self.repo)
            storage.check_declared(a.BASE, self.same, self.repo)

    def test_a_candidate_that_differs_outside_performance_is_refused(self):
        with storage.using_storage_table("task37-t33"):
            with self.assertRaisesRegex(dw.Refusal, "not that of the cand"):
                storage.check_declared(a.BASE, self.other, self.repo)
            with self.assertRaisesRegex(dw.Refusal, "cannot compare"):
                storage.check_declared(a.BASE, "f" * 40, self.repo)
            with self.assertRaisesRegex(dw.Refusal, "for base"):
                storage.check_declared("f" * 40, self.same, self.repo)

    def test_the_c32_table_needs_the_exact_candidate(self):
        storage.check_declared(a.BASE, self.declared, self.repo)
        with self.assertRaisesRegex(dw.Refusal, "for cand"):
            storage.check_declared(a.BASE, self.same, self.repo)


class Records37(unittest.TestCase):
    """What the stage reports and dispositions of the TASK37 tables
    record (and the C32 ones do not)."""

    def test_the_snapshot_tmpdir_follows_the_table(self):
        for name, table in dw.TABLES.items():
            want = snap.TMPDIR if name in ("task32", "task33") else \
                table.scratch + "/tmp"
            self.assertEqual(snap.TABLE_TMPDIR[name], want, name)
        self.assertEqual(snap.TMPDIR, "/dev/shm/t32/tmp")
        self.assertEqual(snap.environment("h")["TMPDIR"], snap.TMPDIR)

    def test_the_build_command_takes_a_table_and_a_tmpdir(self):
        seen = []
        argv = ["build", "--repo", "r", "--manifest", "m", "--root", "x",
                "--evidence", "e", "--scratch", "s", "--side", "base",
                "--pin", "a" * 40]
        for extra, want in (
                ([], snap.TMPDIR),
                (["--table", "task37-t32"], "/dev/shm/t37-t32/tmp"),
                (["--table", "task37-t33"], "/dev/shm/t37-t33/tmp"),
                (["--table", "task37-t33", "--tmpdir", "/z"], "/z")):
            with mock.patch.object(snap, "build_side",
                                   lambda *a_, **k: seen.append(k)), \
                    mock.patch.object(snap.a, "serial_lock"), \
                    mock.patch.object(snap, "real_runner"):
                snap.main(argv + extra)
            self.assertEqual(seen[-1]["tmpdir"], want, extra)

    def test_a_disposition_records_a_task37_table_only(self):
        for name in dw.TABLES:
            with dw.using_table(name):
                self.assertEqual(
                    dw.disposition_table(),
                    {"table": name} if name.startswith("task37-") else {})

    def test_stage_reports_record_the_fixed_ref(self):
        spec = dict(names=[], pairs={}, reps={}, key="k", seed="s")
        for name in ("task32", "task37-t32"):
            with dw.using_table(name):
                report = dw.new_report("smoke", None, spec, "r", {
                    "base": dict(pin="b", root="x"),
                    "cand": dict(pin="c", root="y")}, {}, "o")
            self.assertEqual(report.get("compiled_ref"),
                             dw.TABLES[name].compiled_ref)
            self.assertEqual("compiled_ref" in report, name != "task32")

    def test_the_replay_checks_the_ref_of_the_report(self):
        with tempfile.TemporaryDirectory() as tmp:
            for name, ref in (("task37-t32", None), ("task32", "f" * 40)):
                run = dict(schema=dw.SCHEMA, success=True)
                if name != "task32":
                    run["table"] = name
                if ref:
                    run["compiled_ref"] = ref
                (Path(tmp) / "downstream.json").write_text(json.dumps(run))
                with dw.using_table(name), self.assertRaisesRegex(
                        dw.Refusal, "compiled ref"):
                    dw.replay_one(tmp)

    def test_the_gates_require_the_task37_table_of_a_disposition(self):
        lineage = mock.Mock()
        with tempfile.TemporaryDirectory() as tmp:
            for reader, table in ((gates.read_task32, "task37-t32"),
                                  (gates.read_task33, "task37-t33")):
                for held in ({}, dict(table="task32"),
                             dict(table="task33"), dict(table="other")):
                    path = Path(tmp) / "d.json"
                    path.write_text(json.dumps(held))
                    with self.assertRaisesRegex(ValueError, table):
                        reader(path, lineage)


class OfflineBinding(unittest.TestCase):
    """A report is bound to the declaration it was made under, and the
    selection is scoped; the archive is accepted under its own table."""
    TASK37 = HERE / "task37_declared.json"

    def test_the_selection_is_scoped_even_when_the_command_raises(self):
        before = offline.DECLARED
        with self.assertRaises(RuntimeError):
            with offline.using_declared(self.TASK37):
                self.assertEqual(offline.DECLARED, self.TASK37)
                raise RuntimeError("x")
        self.assertEqual(offline.DECLARED, before)
        with offline.using_declared(None):
            self.assertEqual(offline.DECLARED, before)

    def test_the_code_seals_the_declaration_actually_selected(self):
        own = offline.code_seals()
        self.assertIn("task33_declared.json", own)
        self.assertNotIn("task37_declared.json", own)
        with offline.using_declared(self.TASK37):
            now = offline.code_seals()
            self.assertIn("task37_declared.json", now)
            self.assertNotIn("task33_declared.json", now)
            self.assertEqual(now["task37_declared.json"],
                             a.seal(self.TASK37))
            self.assertEqual(
                {k: v for k, v in now.items() if k != "task37_declared.json"},
                {k: v for k, v in own.items() if k != "task33_declared.json"})
            offline.check_code(now)
            with self.assertRaisesRegex(ValueError, "recorded code is not"):
                offline.check_code(own)
        offline.check_code(own)
        with self.assertRaisesRegex(ValueError, "recorded code is not"):
            offline.check_code(now)

    def test_a_changed_declaration_changes_the_code_check(self):
        with tempfile.TemporaryDirectory() as tmp:
            copy = Path(tmp) / "task37_declared.json"
            copy.write_text(self.TASK37.read_text())
            with offline.using_declared(copy):
                made = offline.code_seals()
                offline.check_code(made)
                copy.write_text(copy.read_text() + " ")
                with self.assertRaisesRegex(ValueError, "changed"):
                    offline.check_code(made)

    def test_only_task33s_declaration_accepts_the_history(self):
        old = dict(offline.code_seals())
        name = "task32_downstream.py"
        old[name] = dw.TASK33_HISTORY[name][0]
        offline.check_code(old)
        # decided by the selected table, not by the declaration's path
        with offline.using_declared(self.TASK37), dw.using_table("task37-t33"):
            seals = offline.code_seals()
            seals[name] = dw.TASK33_HISTORY[name][0]
            with self.assertRaisesRegex(ValueError, "changed"):
                offline.check_code(seals)
        with offline.using_declared(self.TASK37):  # a table with none of its own
            seals = offline.code_seals()
            seals[name] = dw.TASK33_HISTORY[name][0]
            offline.check_code(seals)
        with dw.using_table("task37-t33"):  # the declaration's name is moot
            old = dict(offline.code_seals())
            old[name] = dw.TASK33_HISTORY[name][0]
            with self.assertRaisesRegex(ValueError, "changed"):
                offline.check_code(old)

    def test_a_command_runs_and_writes_under_its_declaration(self):
        seen = []
        args = mock.Mock(command="archive", archive="f", ledger=None,
                         no_replay=True, out="o", declared=self.TASK37)

        def written(*a_):
            seen.append((offline.DECLARED, offline.code_seals()))
            return None
        before = offline.DECLARED
        with mock.patch.object(offline, "archive_report",
                               return_value=({}, {})), \
                mock.patch.object(offline, "write_report", written):
            offline.run(args)
        self.assertEqual(seen[0][0], self.TASK37)
        self.assertIn("task37_declared.json", seen[0][1])
        self.assertEqual(offline.DECLARED, before)

    def test_every_report_command_takes_the_declaration(self):
        parser = offline.build_parser()
        for command, extra in (("archive", ["--archive", "a"]),
                               ("audit", ["--manifest", "m", "--cand-root",
                                          "c", "--base-root", "b"]),
                               ("harvest", ["--manifest", "m", "--cand-root",
                                            "c"])):
            args = parser.parse_args(
                [command, "--out", "o", "--declared", "d.json", *extra])
            self.assertEqual(args.declared, Path("d.json"), command)

    def test_an_archive_is_replayed_under_the_table_of_its_run(self):
        seen = []

        def archived(folder, repo, replay, checks, ledger=None):
            seen.append(dw.ACTIVE.name)
            return dict(folder="f"), {}
        for table, wanted, declared in (
                (None, "task32", None), ("task32", "task32", None),
                ("task37-t32", "task37-t32", self.TASK37)):
            with tempfile.TemporaryDirectory() as tmp, \
                    offline.using_declared(declared or offline.DECLARED):
                run = dict(table=table) if table else {}
                (Path(tmp) / "downstream.json").write_text(json.dumps(run))
                with mock.patch.object(offline, "archive_in_table",
                                       archived):
                    inputs, _ = offline.archive_report(tmp, "r", False, None)
                self.assertEqual(seen[-1], wanted)
                self.assertEqual(dw.ACTIVE.name, "task32")
                # recorded for TASK37's table only: C32 reports as before
                self.assertEqual(inputs.get("table"),
                                 "task37-t32" if declared else None)

    def test_the_archive_is_of_the_table_the_declaration_binds(self):
        for table, declared in (
                ("task32", self.TASK37), ("task37-t32", None),
                (None, self.TASK37), ("task33", None),
                ("task37-t33", self.TASK37), ("task37-t33", None)):
            with tempfile.TemporaryDirectory() as tmp, \
                    offline.using_declared(declared or offline.DECLARED):
                run = dict(table=table) if table else {}
                (Path(tmp) / "downstream.json").write_text(json.dumps(run))
                with self.assertRaisesRegex(ValueError, "binds the archive"):
                    offline.archive_report(tmp, "r", False, None)

    def test_the_archive_report_is_bound_to_table_base_and_candidate(self):
        declared = dict(base=a.BASE, cand="d" * 40)
        with mock.patch.object(offline, "load_declared",
                               return_value=declared):
            def report(**inputs):
                return dict(inputs=inputs)
            # C32: no table recorded, the exact candidate
            storage.check_archive_binding(report(base=a.BASE, cand="d" * 40))
            for bad in (dict(base="b" * 40, cand="d" * 40),
                        dict(base=a.BASE, cand="e" * 40),
                        dict(base=a.BASE, cand="d" * 40,
                             table="task37-t32"),
                        dict(cand="d" * 40), {}):
                with self.assertRaises(ValueError, msg=bad):
                    storage.check_archive_binding(report(**bad))
            with self.assertRaises(ValueError):
                storage.check_archive_binding({})
            # TASK37: its table recorded; base and an equivalent candidate
            with offline.using_declared(self.TASK37), \
                    storage.using_storage_table("task37-t33"):
                task37 = dict(base=a.BASE, cand="d" * 40,
                              table="task37-t32")
                storage.check_archive_binding(report(**task37))
                for bad in (dict(task37, table="task32"),
                            {k: v for k, v in task37.items()
                             if k != "table"},
                            dict(task37, base="b" * 40)):
                    with self.assertRaises(ValueError, msg=bad):
                        storage.check_archive_binding(report(**bad))
                with mock.patch.object(storage, "check_declared",
                                       side_effect=storage.d.Refusal(
                                           "tree differs")) as judged:
                    with self.assertRaisesRegex(ValueError,
                                                "archive report.*tree"):
                        storage.check_archive_binding(report(**task37), "r")
                    judged.assert_called_once_with(a.BASE, "d" * 40, "r")


class GatesRetargeted(unittest.TestCase):
    class Lineage:
        repo = HERE.parents[3]
        candidate = "c" * 40

        def __init__(self, equivalent=True):
            self.ok = equivalent

        def equivalent(self, label, rev):
            if not self.ok:
                raise ValueError("%s: not equivalent" % label)
            return rev

    def test_the_task32_replay_runs_under_the_task37_table(self):
        seen = []

        def chain(*a_):
            seen.append(dw.ACTIVE.name)
            return [dict(report=dict(repo="r"))]
        with tempfile.TemporaryDirectory() as tmp:
            held = Path(tmp) / "d.json"
            held.write_text("{}")
            with mock.patch.object(dw, "replay_chain", chain), \
                    mock.patch.object(dw, "require_ledger"), \
                    mock.patch.object(dw, "ledger_path"), \
                    mock.patch.object(dw, "disposition", return_value={}):
                gates.replay_task32(held, "--stage s", self.Lineage())
        self.assertEqual(seen, ["task37-t32"])
        self.assertEqual(dw.ACTIVE.name, "task32")

    def test_the_task33_replay_runs_under_the_task37_tables(self):
        """`dispatch` is stubbed, so it selects no declaration: what it
        sees is the tables (both drivers' `task37-t33`, the parsed
        `--table`), and the replay restores them (task32 and task33)
        afterwards."""
        seen = []

        def dispatched(args):
            seen.append((dw.ACTIVE.name, storage.ACTIVE_STORAGE, args.table,
                         offline.DECLARED))
            Path(args.out).write_text(json.dumps(dict(candidate="x")))
        with tempfile.TemporaryDirectory() as tmp:
            with dw.using_table("task37-t33"):
                code = dw.code_seals()
            held = Path(tmp) / "d.json"
            held.write_text(json.dumps(dict(candidate="x", code=code)))
            text = "--stage s --timing-stage t --offline o"
            with mock.patch.object(storage, "dispatch", dispatched), \
                    mock.patch.object(gates, "check_declared"):
                gates.replay_task33(held, text, self.Lineage())
                self.assertEqual(seen, [("task37-t33", "task37-t33",
                                         "task37-t33",
                                         offline.DEFAULT_DECLARED)])
        self.assertEqual((dw.ACTIVE.name, storage.ACTIVE_STORAGE),
                         ("task32", "task33"))

    def test_the_replays_refuse_a_table_in_their_arguments(self):
        with tempfile.TemporaryDirectory() as tmp:
            held = Path(tmp) / "d.json"
            held.write_text(json.dumps(dict(candidate="x", code={})))
            for replay, table in ((gates.replay_task32, "task37-t32"),
                                  (gates.replay_task33, "task37-t33")):
                for text in ("--table %s --stage s" % table,
                             "--stage s --table %s" % table,
                             "--stage s --table task32"):
                    with self.assertRaisesRegex(
                            ValueError, "not those of its own command"):
                        replay(held, text, self.Lineage())

    def test_the_task33_replay_refuses_another_declaration(self):
        with tempfile.TemporaryDirectory() as tmp:
            with dw.using_table("task37-t33"):
                code = dw.code_seals()
            held = Path(tmp) / "d.json"
            held.write_text(json.dumps(dict(candidate="x", code=code)))
            text = ("--stage s --timing-stage t --offline o --declared " +
                    str(HERE / "task33_declared.json"))
            with self.assertRaisesRegex(ValueError, "contradicts"):
                gates.replay_task33(held, text, self.Lineage())

    def test_the_declaration_may_name_an_equivalent_candidate(self):
        path = HERE / "task37_declared.json"
        declared = json.loads(path.read_text())
        held = dict(candidate="d" * 40)
        with mock.patch.object(offline, "shape_problems", return_value=[]):
            gates.check_declared(dict(candidate=declared["cand"]), path,
                                 self.Lineage(False))
            gates.check_declared(held, path, self.Lineage(True))
            with self.assertRaisesRegex(ValueError, "candidate"):
                gates.check_declared(held, path, self.Lineage(False))
            with self.assertRaises(TypeError):  # the lineage is required
                gates.check_declared(held, path)


class ReceiptCandidate(unittest.TestCase):
    CAND = "a" * 40

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def builds(self, cand, name="builds.json"):
        path = self.root / name
        path.write_text(json.dumps(dict(
            schema="task37-builds-v1", pins=dict(base=a.BASE, cand=cand))))
        return path

    def test_the_candidate_must_be_the_one_the_builds_measured(self):
        report = self.builds(self.CAND)
        for candidate in (self.CAND, self.CAND[:12]):
            made = gates.make_receipt(gates.D7, candidate, "pass", 0,
                                      [report])
            self.assertEqual(made["candidate"], candidate)
        for candidate in ("b" * 40, "b" * 12, self.CAND[:6]):
            with self.assertRaisesRegex(ValueError, "measured"):
                gates.make_receipt(gates.D7, candidate, "pass", 0, [report])

    def test_reports_that_are_not_builds_data_are_not_examined(self):
        other = self.root / "other.json"
        other.write_text(json.dumps(dict(schema="x", note="c")))
        listed = self.root / "list.json"
        listed.write_text("[1]")
        gates.make_receipt(gates.D7, self.CAND, "pass", 0, [
            self.builds(self.CAND), other, listed])

    def test_an_unreadable_or_non_json_report_is_refused(self):
        plain = self.root / "plain.txt"
        plain.write_text("not json")
        for report in (plain, self.root / "missing.json"):
            with self.assertRaisesRegex(ValueError, "not readable JSON"):
                gates.make_receipt(gates.D7, self.CAND, "pass", 0, [
                    self.builds(self.CAND), report])

    def test_one_report_is_the_builds_receipt(self):
        attribution = self.root / "attribution.json"
        attribution.write_text(json.dumps(dict(
            schema="task37-builds-v1-attribution",
            pins=dict(base=a.BASE, cand=self.CAND))))
        with self.assertRaisesRegex(ValueError, "build-timing receipt"):
            gates.make_receipt(gates.D7, self.CAND, "pass", 0,
                               [attribution])
        gates.make_receipt(gates.D7, self.CAND, "pass", 0,
                           [self.builds(self.CAND), attribution])

    def test_the_attribution_output_is_examined_too(self):
        for schema, cand in (("task37-builds-v1-attribution", "b" * 40),
                             ("other", "b" * 40)):  # any report with pins
            bad = self.root / "bad.json"
            bad.write_text(json.dumps(dict(
                schema=schema, pins=dict(base=a.BASE, cand=cand))))
            with self.assertRaisesRegex(ValueError, "measured"):
                gates.make_receipt(gates.D7, self.CAND, "pass", 0,
                                   [self.builds(self.CAND), bad])

    def test_the_baseline_must_be_the_one_of_the_task(self):
        for pins in (dict(base="b" * 40, cand=self.CAND),
                     dict(cand=self.CAND), None):
            bad = self.root / "bad.json"
            bad.write_text(json.dumps(dict(schema="task37-builds-v1",
                                           pins=pins)))
            with self.assertRaisesRegex(ValueError, "baseline|no pins"):
                gates.make_receipt(gates.D7, self.CAND, "pass", 0, [bad])

    def test_every_builds_report_is_checked(self):
        with self.assertRaisesRegex(ValueError, "measured"):
            gates.make_receipt(gates.D7, self.CAND, "pass", 0, [
                self.builds(self.CAND), self.builds("b" * 40, "two.json")])

    def test_a_loaded_receipt_is_checked_again(self):
        report = self.builds(self.CAND)
        made = gates.make_receipt(gates.D7, self.CAND, "pass", 0, [report])
        path = self.root / "r.json"
        a.save(path, made)
        gates.load_receipt(path, self.Lineage())
        path = self.root / "r2.json"
        a.save(path, dict(made, candidate="b" * 40))
        with self.assertRaisesRegex(ValueError, "measured"):
            gates.load_receipt(path, self.Lineage())

    class Lineage:
        def candidate_of(self, label, rev):
            return rev


class HistoryOfTheKeptRecords(unittest.TestCase):
    """The histories hold the seals of the versions the kept records were
    made with (7e202dfbaa) and no intermediate version."""
    KEPT = "7e202dfbaa63a48514c36fece89e3ab3f69b3696"
    PERF = "src/simp/tests/performance/"
    FILES = ("task32_downstream.py", "task32_snapshots.py",
             "task33_offline.py", "task33_storage.py", "task33_rules.py",
             "task33_dispose.py")

    def seal_at(self, rev, name):
        data = subprocess.run(
            ["git", "-C", str(HERE), "show", "%s:%s%s" % (
                rev, self.PERF, name)], stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
        if data.returncode != 0:
            self.skipTest("%s:%s is not in this repository" % (rev, name))
        import hashlib
        return dict(sha256=hashlib.sha256(data.stdout).hexdigest(),
                    bytes=len(data.stdout))

    def test_the_kept_versions_are_in_the_histories(self):
        for name in self.FILES:
            seal = self.seal_at(self.KEPT, name)
            history = dw.TASK33_HISTORY[name]
            self.assertIn(seal, history, name)
            if name in dw.TASK32_HISTORY:
                self.assertIn(seal, dw.TASK32_HISTORY[name], name)

    def test_no_later_version_is_in_a_history(self):
        """A history holds the seals of the versions the kept records were
        made with: the version at KEPT, and no seal of any other version
        since (a later version whose content equals a kept one is the
        kept version and is fine)."""
        listed = subprocess.run(
            ["git", "-C", str(HERE), "rev-list", self.KEPT + "..HEAD",
             "--", *(self.PERF + n for n in self.FILES)],
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL)
        if listed.returncode != 0:
            self.skipTest("%s is not in this repository" % self.KEPT)
        for name in self.FILES:
            kept = self.seal_at(self.KEPT, name)
            for rev in listed.stdout.decode().split():
                seal = self.seal_at(rev, name)
                if seal == kept:
                    continue
                for history in (dw.TASK32_HISTORY, dw.TASK33_HISTORY):
                    self.assertNotIn(seal, history.get(name, []),
                                     (rev, name))

    def test_the_task37_tables_have_no_history(self):
        for name in ("task37-t32", "task37-t33"):
            self.assertEqual(dw.TABLES[name].history, {})


if __name__ == "__main__":
    unittest.main()
