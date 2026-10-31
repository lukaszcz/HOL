#!/usr/bin/env python3
"""TASK29B allocation matrix driver: Grid, run, resume, check-jobs, seals.

The real Grid.cell, Grid.process, Grid.audit, Grid.reseal, run, finish and
check_jobs run against a sandbox of tiny files and a stub executor; no
runtime, toolchain or committed receipt is used.
"""
import argparse
import contextlib
import gzip
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import tempfile
import time
import unittest
from unittest import mock

import acceptance as a
import allocation_matrix as m
import allocation_schema as sc
import allocation_testbed as tb
import evidence_bundle as bundle
import loading
import test_allocator_path_guards as guards
from allocation_testbed import CASE

REAL = m.Grid
FAILURES = (sc.InvalidAllocation, m.rp.InvalidRun)
TREE = "d" * 64  # invented: tree identity outside the performance area


def harness(**change):
    """Invented harness record of a controls receipt (see run_controls)."""
    return dict(dict(head=tb.CAND_PIN, dirty=False, reference="simplifier",
                     reference_commit="c" * 40, tree_outside_performance=TREE),
                **change)


def lineage(**change):
    found = dict(dict(hol_snapshot=tb.CAND_PIN,
                      native_configuration="config\n",
                      hol_products={"/x/bin/hol": dict(sha256="1", bytes=1)},
                      native_products={"/x/bin/poly": dict(sha256="2",
                                                           bytes=2)}),
                 **change)
    return {k: v for k, v in found.items() if v is not ...}


CELLS = ["frag_create-0", "frag_create-1", "frag_create-10",
         "frag_create-100"]


def make_stub(sb, change=None, boom=None, delay=0):
    """A Grid whose processes are synthetic receipts of the sandbox."""
    log = dict(calls=[], exits=[], cells=[], jobs=[])

    class Stub(REAL):
        def __init__(self, args):
            self.args, self.pairs = args, args.pairs
            self.report = dict(commands=[])
            self.scratch, self.ready = None, False
            self.env = dict(TMPDIR=str(sb.root))
            self.header = {k: v for k, v in sb.header().items()
                           if k != "iterations"}

        def __enter__(self):
            return self

        def __exit__(self, *exc):
            log["exits"].append(exc[0])
            return False

        def make_job(self, index):
            self.report["commands"].append(dict(command=["Holmake"],
                                                exit=0, index=index))
            log["jobs"].append(index)
            return sb.job()

        def process(self, job, experiment, side, case, size, pair, steady,
                    repeats):
            log["calls"].append((experiment, side, pair))
            extra = (change(self, experiment, side, pair) if change
                     else None) or {}
            return sb.receipt(experiment, side, pair, 0, case, size, steady,
                              repeats, **extra)

        def cell(self, job, case, size, root, counts):
            log["cells"].append(m.name_of(case, size))
            if boom and boom(case, size):
                raise RuntimeError("cell exploded")
            time.sleep(delay)
            return REAL.cell(self, job, case, size, root, counts)
    return Stub, log


def arguments(output, only=None, **kw):
    values = dict(output=Path(output), only=only or [], resume=False, jobs=2,
                  pairs=2, timeout=60,
                  # the receipt of the sandbox next to the output directory
                  controls_receipt=Path(output).parent / "sb" /
                  "controls.json")
    values.update(kw)
    return argparse.Namespace(**values)


class Bed(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.sb = tb.Sandbox(self.root / "sb", pairs=2)
        self.out = self.root / "out"

    def patched(self, change=None, boom=None, delay=0):
        stub, log = make_stub(self.sb, change, boom, delay)
        patcher = mock.patch.object(m, "Grid", stub)
        patcher.start()
        self.addCleanup(patcher.stop)
        return log

    def quiet(self, function, *args):
        with contextlib.redirect_stdout(io.StringIO()):
            return function(*args)


class Cell(Bed):
    def grid(self, **kw):
        stub, log = make_stub(self.sb, **kw)
        grid = stub(arguments(self.out))
        return grid, log

    def test_cell_runs_ab_ba_pairs_and_archives_them(self):
        grid, log = self.grid()
        self.out.mkdir()
        row = grid.cell(self.sb.job(), CASE, 0, self.out,
                        m.load_iterations())
        self.assertEqual((row["status"], row["rejected"], row["files"]),
                         ("pass", None, 9))
        self.assertEqual(log["calls"], [
            ("candidate", "baseline", 0), ("candidate", "candidate", 0),
            ("candidate", "candidate", 1), ("candidate", "baseline", 1),
            ("control", "baseline", 0), ("control", "control", 0),
            ("control", "control", 1), ("control", "baseline", 1)])
        folder = self.root / "unpacked"
        bundle.unpack(self.out / row["archive"], folder)
        meta = a.load(folder / "meta.json.gz")
        self.assertEqual(meta["rejected"], None)
        self.assertEqual(meta["pairs"], 2)
        record = a.load(folder / "control/pair-01-sel-b1.json.gz")
        self.assertEqual((record["side"], record["position"]),
                         ("control", 0))
        self.assertEqual(a.seal(self.out / row["archive"]), row["seal"])
        self.assertEqual(sorted(p.name for p in self.out.iterdir()),
                         [CASE + "-0.json.xz"])

    def test_rejected_process_ends_the_cell_and_is_archived(self):
        def change(grid, experiment, side, pair):
            if (experiment, side, pair) == ("candidate", "candidate", 1):
                return dict(mutate=lambda events: events.__setitem__(
                    slice(None), events[:6]))
        grid, log = self.grid(change=change)
        self.out.mkdir()
        # The synthetic process itself never rejects: only the offline
        # replay does. That is a rejected, archived cell with its reason,
        # never an aborted run that loses the cells already measured.
        row = grid.cell(self.sb.job(), CASE, 0, self.out,
                        m.load_iterations())
        self.assertEqual(row["status"], "unresolved")
        self.assertTrue(row["rejected"])
        self.assertTrue((self.out / row["archive"]).exists())
        self.assertEqual(row["files"], 9)
        folder = self.root / "unpacked"
        bundle.unpack(self.out / row["archive"], folder)
        self.assertEqual(a.load(folder / "meta.json.gz")["rejected"], None)

    def test_a_replay_failure_of_any_kind_rejects_only_its_cell(self):
        grid, _ = self.grid()
        self.out.mkdir()
        for label, error in (
                ("allocation", sc.InvalidAllocation("replay says no")),
                ("run", m.rp.InvalidRun("replay run says no")),
                ("os", OSError("replay file gone"))):
            with self.subTest(label), mock.patch.object(
                    m, "replay_cell", side_effect=error):
                row = grid.cell(self.sb.job(), CASE, 0, self.out,
                                m.load_iterations())
                self.assertIn("says no" if label != "os"
                              else "gone", row["rejected"])
                self.assertEqual(row["status"], "unresolved")

    def test_a_process_the_grid_rejected_is_kept_with_its_reason(self):
        stub, log = make_stub(self.sb)

        class Rejecting(stub):
            def process(self, job, experiment, side, case, size, pair,
                        steady, repeats):
                receipt = super().process(job, experiment, side, case, size,
                                          pair, steady, repeats)
                if (experiment, side, pair) == ("candidate", "candidate", 1):
                    receipt.update(accepted=False, rejection="boom")
                return receipt
        grid = Rejecting(arguments(self.out))
        self.out.mkdir()
        row = grid.cell(self.sb.job(), CASE, 0, self.out,
                        m.load_iterations())
        self.assertEqual((row["status"], row["rejected"]),
                         ("unresolved", "boom"))
        self.assertEqual(len(log["calls"]), 3)  # nothing runs after it
        folder = self.root / "unpacked"
        bundle.unpack(self.out / row["archive"], folder)
        self.assertEqual(a.load(folder / "meta.json.gz")["rejected"], "boom")

    def test_private_selection_changed_by_a_process_is_rejected(self):
        def change(grid, experiment, side, pair):
            if (experiment, side, pair) == ("control", "control", 0):
                (self.sb.private["control"] / "Traverse.sml").write_text("x")
        grid, _ = self.grid(change=change)
        self.out.mkdir()
        row = grid.cell(self.sb.job(), CASE, 0, self.out,
                        m.load_iterations())
        self.assertEqual(row["status"], "unresolved")
        self.assertIn("private selection changed", row["rejected"])

    def test_loaded_input_changed_after_the_processes_is_rejected(self):
        grid, _ = self.grid()
        self.out.mkdir()
        audit = grid.audit

        def tampering(job, folder):
            (self.sb.repo / "src/Heap1.uo").write_text("changed\n")
            audit(job, folder)
        grid.audit = tampering
        row = grid.cell(self.sb.job(), CASE, 0, self.out,
                        m.load_iterations())
        self.assertIn("changed during cell", row["rejected"])

    def test_every_shared_input_is_checked_again_after_the_cell(self):
        shared = set()
        receipt = self.sb.receipt("candidate", "baseline", 0, 0)
        for info in receipt["paths"].values():
            if not any(info["physical"].startswith(str(d) + "/")
                       for d in self.sb.private.values()):
                shared.add(info["physical"])
                shared.update(info["related_products"])
        self.assertGreaterEqual(len(shared), 2)
        for index, physical in enumerate(sorted(shared)):
            with self.subTest(physical=physical):
                path = Path(physical)
                original = path.read_bytes()
                self.addCleanup(path.write_bytes, original)
                grid, _ = self.grid()
                out = self.root / ("out%d" % index)
                out.mkdir()
                audit = grid.audit

                def tampering(job, folder, path=path, audit=audit):
                    path.write_bytes(path.read_bytes() + b"x")
                    audit(job, folder)
                grid.audit = tampering
                row = grid.cell(self.sb.job(), CASE, 0, out,
                                m.load_iterations())
                path.write_bytes(original)
                self.assertIn("changed during cell", row["rejected"])

    def test_files_that_cannot_be_read_reject_the_cell(self):
        stub, _ = make_stub(self.sb)

        class Unreadable(stub):
            def process(self, *args):
                raise OSError("disk gone")
        out = self.root / "unreadable"
        out.mkdir()
        row = Unreadable(arguments(out)).cell(
            self.sb.job(), CASE, 0, out, m.load_iterations())
        self.assertEqual((row["status"], row["rejected"]),
                         ("unresolved", "disk gone"))

    def test_the_archive_must_unpack_to_the_original_bytes(self):
        grid, _ = self.grid()
        real = m.bundle.unpack

        def corrupting(archive, dst):
            count = real(archive, dst)
            if Path(dst).name == "roundtrip":
                target = Path(dst) / "meta.json.gz"
                target.write_bytes(target.read_bytes() + b"x")
            return count
        self.out.mkdir()
        with mock.patch.object(m.bundle, "unpack", corrupting):
            with self.assertRaisesRegex(sc.InvalidAllocation,
                                        "transport changed"):
                grid.cell(self.sb.job(), CASE, 0, self.out,
                          m.load_iterations())

    def test_the_row_status_is_the_replayed_decision(self):
        def more(grid, experiment, side, pair):
            if side == "candidate":
                return dict(work={"apply": {"native": 5}})

        def drift(grid, experiment, side, pair):
            if side == "control" and pair == 0:
                return dict(work={"apply": {"native": 5}})
        for label, change, status in (("fail", more, "fail"),
                                      ("inconclusive", drift,
                                       "inconclusive")):
            with self.subTest(label):
                grid, _ = self.grid(change=change)
                out = self.root / label
                out.mkdir()
                row = grid.cell(self.sb.job(), CASE, 0, out,
                                m.load_iterations())
                self.assertEqual(row["status"], status)

    def test_uncaught_errors_are_not_swallowed(self):
        def change(grid, experiment, side, pair):
            raise KeyError("bug")
        grid, _ = self.grid(change=change)
        self.out.mkdir()
        with self.assertRaises(KeyError):
            grid.cell(self.sb.job(), CASE, 0, self.out, m.load_iterations())


class Commands(unittest.TestCase):
    """The driver's own subprocess wrapper and the grid header."""

    def grid(self):
        grid = REAL.__new__(REAL)
        grid.args = argparse.Namespace(timeout=5)
        grid.hol, grid.fds, grid.report = Path("."), (), dict(commands=[])
        grid.env = dict(PATH=os.environ["PATH"])
        return grid

    def result(self, **kw):
        return dict(dict(exit=0, timed_out=False, stdout=""), **kw)

    def test_a_failing_or_timed_out_command_is_an_error(self):
        grid = self.grid()
        for label, change in (("exit", dict(exit=1)),
                              ("timeout", dict(timed_out=True))):
            with self.subTest(label):
                with mock.patch.object(m.loading, "execute",
                                       return_value=self.result(**change)):
                    with self.assertRaisesRegex(sc.InvalidAllocation,
                                                "failed command"):
                        grid.run(["x"])
        self.assertEqual(len(grid.report["commands"]), 2)  # both recorded
        with mock.patch.object(m.loading, "execute",
                               return_value=self.result()):
            grid.run(["y"])
        self.assertEqual(len(grid.report["commands"]), 3)

    def test_header_binds_the_controls_receipt_to_this_runtime(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        sb = tb.Sandbox(Path(tmp.name) / "sb", pairs=2)
        header = sb.header()
        grid = sb.real_grid()
        with grid.make():
            found = grid.make_header(tb.CAND_PIN,
                                     header["toolchain_products"])
        runtime = tb.RUNTIME
        self.assertEqual(found["controls"]["runtime"], runtime)
        self.assertEqual(found["controls"]["receipt"],
                         a.seal(sb.controls_path))
        self.assertEqual(found["controls"]["file"], "controls-receipt.json")
        self.assertEqual(found["runtime"], runtime)
        self.assertEqual(found["shim"], header["shim"])
        self.assertTrue(set(tb.EXPECTED_GRID_KEYS) <= set(found) | {
            "iterations"})
        for key in tb.EXPECTED_GRID_KEYS:
            if key not in ("iterations", "controls"):
                self.assertEqual(found[key], header[key], key)
        self.assertEqual(found["environment"], sb.content_environment())
        self.assertNotIn("TMPDIR", found["environment"])
        self.assertEqual(found["tmpdir"], sb.base_environment()["TMPDIR"])
        grid.report = dict(runtime=dict(runtime, bytes=8),
                           shim=header["shim"])
        with grid.make(), self.assertRaisesRegex(
                sc.InvalidAllocation, "different runtime"):
            grid.make_header(tb.CAND_PIN, header["toolchain_products"])
        # The candidate must equal the harness outside the performance area.
        grid.report = dict(runtime=runtime, shim=header["shim"])
        with mock.patch.object(m.pr, "tree_outside_performance",
                               return_value="e" * 64), \
                self.assertRaisesRegex(sc.InvalidAllocation,
                                       "differs from the candidate"):
            grid.make_header(tb.CAND_PIN, header["toolchain_products"])
        # The receipt's build must be this toolchain's own.
        for label, change, message in (
                ("libraries", lambda g: g.libraries.update(
                    {"/usr/lib/libc.so.6": dict(sha256="e" * 64, bytes=3)}),
                 "other instrumented libraries"),
                ("configuration", lambda g: setattr(
                    g, "native_configuration", "other\n"),
                 "another native Poly/ML configuration")):
            with self.subTest(label):
                other = sb.real_grid()
                change(other)
                with other.make(), self.assertRaisesRegex(
                        sc.InvalidAllocation, message):
                    other.make_header(tb.CAND_PIN,
                                      header["toolchain_products"])


class Placement(unittest.TestCase):
    """What a resume may ignore (where things stand) and what it may not."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.sb = tb.Sandbox(self.root / "sb", pairs=2)
        self.products = self.sb.header()["toolchain_products"]

    def moved_tmpdir(self):
        """Another scratch place of the length of the sandbox's."""
        return str(self.root / "sb")[:-2] + "s2"

    def made(self, **kw):
        grid = self.sb.real_grid(**kw)
        with grid.make():
            return grid, self.header(grid)

    def header(self, grid):
        """As run() completes it: with the iteration counts."""
        return dict(grid.make_header(tb.CAND_PIN, self.products),
                    iterations=tb.counts())

    def test_the_key_lists_are_what_the_tests_say(self):
        self.assertEqual(sorted(m.GRID_KEYS), sorted(tb.EXPECTED_GRID_KEYS))
        self.assertEqual(sorted(m.PLACE_KEYS),
                         sorted(tb.EXPECTED_PLACE_KEYS))
        self.assertFalse(set(m.GRID_KEYS) & set(m.PLACE_KEYS))
        self.assertEqual(sorted(m.LENGTH_KEYS),
                         sorted(tb.EXPECTED_LENGTH_KEYS))
        self.assertTrue(set(m.LENGTH_KEYS) <= set(m.PLACE_KEYS))
        _, header = self.made()
        self.assertTrue(set(m.GRID_KEYS) | set(m.PLACE_KEYS) <= set(header))

    def test_two_real_headers_that_differ_only_by_place_agree(self):
        moved = self.root / "moved-bracket.so"
        moved.write_bytes(self.sb.shim.read_bytes())
        _, here = self.made()
        _, there = self.made(
            library="/elsewhr/libpolyml.so.16.0.0",
            aliases=["/elsewhr/libpolyml.so.16"], shim=moved,
            tmpdir=self.moved_tmpdir())
        for key in m.PLACE_KEYS:
            self.assertNotEqual(here[key], there[key], key)
        for key in m.GRID_KEYS:
            self.assertEqual(here[key], there[key], key)
        self.assertEqual(m.grid_digest(here), m.grid_digest(there))
        self.assertEqual(m.changed_settings(here, there), [])
        # the private runtime is sealed once, as `runtime`, not as a path
        for header in (here, there):
            self.assertFalse([k for k in header["tools"]
                              if k.endswith("libpolyml.so.16.0.0")])
        # cells measured at different places are bound to their own
        for case, header in (("here", here), ("there", there)):
            bound = m.binding(header, tb.CASE, tb.SIZE)
            self.assertEqual(bound["shim"], header["shim_path"], case)
            self.assertEqual(bound["library"], header["library"], case)
        self.assertNotEqual(m.binding(here, tb.CASE, tb.SIZE),
                            m.binding(there, tb.CASE, tb.SIZE))
        self.assertEqual(
            m.binding(there, tb.CASE, tb.SIZE, m.places(here))["shim"],
            here["shim_path"])
        self.assertEqual(m.binding(there, tb.CASE, tb.SIZE,
                                   m.places(here))["grid"],
                         m.binding(here, tb.CASE, tb.SIZE)["grid"])

    def test_the_environment_but_for_the_scratch_place_is_content(self):
        _, here = self.made()
        for key, value in (("PATH", "/home/x/bin:" + m.pr.PATH),
                           ("CC", "/other/gcc"), ("HOLDIR", "/other/hol"),
                           ("HOME", "/root")):
            with self.subTest(key):
                _, there = self.made(**{key: value})
                self.assertEqual(m.changed_settings(here, there),
                                 ["environment"])
                self.assertNotEqual(m.grid_digest(here),
                                    m.grid_digest(there))
        # TMPDIR is where scratch trees stand, not a difference of content
        _, there = self.made(tmpdir=self.moved_tmpdir())
        self.assertEqual(m.changed_settings(here, there), [])
        self.assertEqual(m.grid_digest(here), m.grid_digest(there))
        self.assertNotEqual(here["tmpdir"], there["tmpdir"])

    def test_a_difference_of_content_is_still_a_difference(self):
        _, here = self.made()
        other = self.root / "other-bracket.so"
        other.write_text("a different shim\n")
        grid, there = self.made(shim=other)
        # the shim is sealed by content: the seal differs, so must the grid
        grid.report["shim"] = a.seal(other)
        with grid.make():
            there = self.header(grid)
        self.assertEqual(m.changed_settings(here, there), ["shim"])
        grid.report = dict(runtime=dict(tb.RUNTIME, bytes=99),
                           shim=here["shim"])
        runtime = dict(tb.controls_data(runtime=dict(tb.RUNTIME, bytes=99)))
        path = self.root / "other-controls.json"
        path.write_text(json.dumps(runtime))
        grid.args.controls_receipt = path
        with grid.make():
            there = self.header(grid)
        self.assertEqual(sorted(m.changed_settings(here, there)),
                         ["controls", "runtime"])

    def test_every_grid_key_is_compared_and_no_place_key_is(self):
        _, here = self.made()
        for key in m.GRID_KEYS:
            with self.subTest(key):
                self.assertEqual(m.changed_settings(
                    here, dict(here, **{key: "changed"})), [key])
        for key in m.PLACE_KEYS:
            with self.subTest(key):
                changed = (["x" * len(v) for v in here[key]]
                           if isinstance(here[key], list)
                           else "x" * len(here[key]))
                self.assertEqual(m.changed_settings(
                    here, dict(here, **{key: changed})), [])

    def test_a_place_of_another_length_is_refused_on_resume(self):
        _, here = self.made()
        for key in m.LENGTH_KEYS:
            for text in (here[key] + "x", here[key][:-1]):
                with self.subTest(key=key, text=text):
                    self.assertEqual(m.changed_settings(
                        here, dict(here, **{key: text})), [key + "-length"])
        # a path that moves into a symlinked directory of another length
        # is seen in the resolved runtime path, with TMPDIR unchanged
        self.assertEqual(m.changed_settings(here, dict(
            here, library="/a/libpolyml.so.16.0.0")), ["library-length"])
        # a header without the place at all is not equal in length
        older = {k: v for k, v in here.items() if k != "tmpdir"}
        self.assertEqual(m.changed_settings(older, here), ["tmpdir-length"])
        self.assertEqual(m.changed_settings(older, dict(here, tmpdir="")),
                         ["tmpdir-length"])
        both = dict(here, tmpdir=here["tmpdir"] + "x",
                    library=here["library"] + "x")
        self.assertEqual(m.changed_settings(here, both),
                         ["tmpdir-length", "library-length"])
        older = {k: v for k, v in here.items() if k != "harness"}
        self.assertEqual(m.changed_settings(older, here), ["harness"])


class Jobs(unittest.TestCase):
    """Grid.make_job and Grid.check_sides over a stubbed checkout."""
    REVS = dict(baseline="a" * 40, control="a" * 40, candidate="b" * 40)

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        self.hol = root / "hol"
        (self.hol / "bin").mkdir(parents=True)
        self.launcher = "%s --gcthreads=1 run --holstate=%s\n" % (
            self.hol / "bin/hol", self.hol / "bin/hol.state0")
        self.item = dict(git_path="src/Foo.sml", sha256="1" * 64, bytes=9,
                         git_blob="2" * 40)
        grid = REAL.__new__(REAL)
        grid.scratch, grid.hol = root / "scratch", self.hol
        grid.scratch.mkdir()
        grid.revisions = dict(self.REVS)
        grid.sources = {side: m.source_map([self.item]) for side in m.SIDES}
        self.sources = grid.sources
        self.grid = grid
        self.checked_out = []

        def checkout(side, directory):
            directory.mkdir()
            (directory / "Foo.sml").write_text("val x = 1\n")
            self.checked_out.append(side)
            return self.REVS[side], [self.item]

        def run(command, cwd):
            directory = Path(command[command.index("-C") + 1])
            (directory / "paired.exe").write_text(self.launcher)
        grid.checkout, grid.run = checkout, run

    def test_a_job_installs_the_fixtures_and_seals_every_side(self):
        job = self.grid.make_job(0)
        self.assertEqual(sorted(job.dirs), sorted(m.SIDES))
        self.assertEqual(sorted(self.checked_out), sorted(m.SIDES))
        for side, directory in job.dirs.items():
            self.assertEqual(directory.name, m.SIDES[side])
            self.assertEqual((directory / "Performance.sml").read_bytes(),
                             (m.HERE / "MatrixAllocation.sml").read_bytes())
            self.assertEqual((directory / "MatrixSupport.sml").read_bytes(),
                             (m.HERE / "MatrixSupport.sml").read_bytes())
            self.assertIn("paired.exe: Performance.uo",
                          (directory / "Holmakefile").read_text())
            self.assertEqual(set(job.tree[side]), {
                p.name for p in directory.iterdir() if p.is_file()})
        self.assertEqual(job.names, {"Foo"})
        self.assertTrue(job.sources)

    def test_a_checkout_that_differs_from_the_grid_is_refused(self):
        for label, change in (
                ("revision", lambda g: g.revisions.update(
                    candidate="c" * 40)),
                ("sources", lambda g: g.sources.update(
                    control=dict(g.sources["control"], x={})))):
            with self.subTest(label):
                self.setUp()
                change(self.grid)
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "differs from the grid"):
                    self.grid.make_job(0)

    def test_a_launcher_with_other_runtime_or_options_is_refused(self):
        for label, old, new in (("options", "--gcthreads=1", ""),
                                ("heap", "hol.state0", "other"),
                                ("runtime", "bin/hol ", "bin/x ")):
            with self.subTest(label):
                self.setUp()
                self.launcher = self.launcher.replace(old, new)
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "unexpected launcher"):
                    self.grid.make_job(0)

    def test_the_three_sides_must_be_what_was_promised(self):
        self.grid.check_sides()
        same = dict(self.REVS, candidate=self.REVS["baseline"])
        for label, change in (
                ("candidate is the baseline", lambda g: g.revisions.update(
                    same)),
                ("control revision", lambda g: g.revisions.update(
                    control="c" * 40)),
                ("control sources", lambda g: g.sources.update(
                    control={}))):
            with self.subTest(label):
                self.setUp()
                change(self.grid)
                with self.assertRaises(sc.InvalidAllocation):
                    self.grid.check_sides()


class Run(Bed):
    def run_cells(self, only, **kw):
        return self.quiet(m.run, arguments(self.out, only, **kw))

    def test_run_writes_inventory_decisions_and_build_receipt(self):
        log = self.patched()
        code = self.run_cells(CELLS[:2])
        self.assertEqual(code, 2)  # a partial smoke never decides
        inventory = a.load(self.out / "inventory.json")
        self.assertEqual(sorted(r["case"] + "-%d" % r["size"]
                                for r in inventory["runs"]), CELLS[:2])
        self.assertEqual(inventory["jobs"], [2])
        self.assertEqual(set(log["jobs"]), {0, 1})
        decisions = a.load(self.out / "decisions-partial.json")
        self.assertEqual((decisions["status"], decisions["complete"]),
                         ("inconclusive", False))
        self.assertTrue((self.out / "RESULTS-partial.md").exists())
        build = a.load(self.out / "build-1.json.gz")
        self.assertEqual([c["index"] for c in build["commands"]
                          if "index" in c].count(0), 1)
        args = type("Args", (), {"output": self.out})
        self.assertEqual(self.quiet(m.replay, args), 2)
        self.assertEqual(log["exits"], [None])

    def test_workers_recorded_are_the_ones_really_used(self):
        self.patched()
        self.run_cells(CELLS[:1], jobs=8)
        self.assertEqual(a.load(self.out / "inventory.json")["jobs"], [1])

    def test_unknown_only_cell_is_rejected(self):
        self.patched()
        with self.assertRaisesRegex(sc.InvalidAllocation, "unknown"):
            self.run_cells(["frag_create-7"])

    def test_output_is_exclusive_create(self):
        self.patched()
        self.out.mkdir()
        with self.assertRaises(FileExistsError):
            self.run_cells(CELLS[:1])

    def test_build_receipt_keeps_private_build_commands_even_on_failure(self):
        stub, _ = make_stub(self.sb)

        class Broken(stub):
            def make_job(self, index):
                super().make_job(index)
                raise RuntimeError("Holmake failed")
        with mock.patch.object(m, "Grid", Broken):
            with self.assertRaises(RuntimeError):
                self.run_cells(CELLS[:1])
        build = a.load(self.out / "build-1.json.gz")
        self.assertEqual(build["commands"][0]["command"], ["Holmake"])

    def test_resume_completes_a_partial_run_and_keeps_history(self):
        self.patched()
        self.run_cells(CELLS[:2])
        (self.out / "stale.json.xz.partial").write_text("x")
        log = self.patched()
        self.quiet(m.run, arguments(self.out, CELLS[:4], resume=True,
                                    jobs=1))
        inventory = a.load(self.out / "inventory.json")
        self.assertEqual(len(inventory["runs"]), 4)
        self.assertEqual(inventory["jobs"], [2, 1])
        self.assertEqual(sorted(log["cells"]), sorted(CELLS[2:4]))
        self.assertTrue((self.out / "build-2.json.gz").exists())
        self.assertFalse((self.out / "stale.json.xz.partial").exists())
        args = type("Args", (), {"output": self.out})
        self.assertEqual(self.quiet(m.replay, args), 2)

    def test_resume_refuses_any_change_of_the_shared_inputs(self):
        self.patched()
        self.run_cells(CELLS[:1])
        before = (self.out / "inventory.json").read_bytes()
        for key in tb.EXPECTED_GRID_KEYS:
            if key == "iterations":
                continue
            with self.subTest(key):
                stub, _ = make_stub(self.sb)

                class Changed(stub):
                    def __init__(self, args, key=key):
                        super().__init__(args)
                        self.header[key] = "changed"
                with mock.patch.object(m, "Grid", Changed):
                    with self.assertRaisesRegex(
                            sc.InvalidAllocation,
                            "resume with different settings.*" + key):
                        self.quiet(m.run, arguments(self.out, CELLS[:2],
                                                    resume=True))
        counts = m.load_iterations()
        counts["steady"] = dict(counts["steady"], **{"frag_create-0": 99})
        self.patched()
        with mock.patch.object(m, "load_iterations",
                              lambda **task: counts):
            with self.assertRaisesRegex(sc.InvalidAllocation, "iterations"):
                self.quiet(m.run, arguments(self.out, CELLS[:2],
                                            resume=True))
        self.assertEqual((self.out / "inventory.json").read_bytes(), before)

    def test_resume_does_not_care_where_the_private_runtime_stands(self):
        self.patched()
        self.run_cells(CELLS[:1])
        # a new session builds its runtime and shim in another scratch
        # tree: only the places differ, the sealed contents are the same
        moved = Path(self.sb.shim).with_name("moved-bracket.so")
        moved.write_bytes(self.sb.shim.read_bytes())
        shim = self.sb.shim
        self.addCleanup(setattr, self.sb, "shim", shim)
        self.sb.shim = moved
        log = self.patched()
        self.quiet(m.run, arguments(self.out, CELLS[:2], resume=True))
        inventory = a.load(self.out / "inventory.json")
        self.assertEqual(sorted(log["cells"]), sorted(CELLS[1:2]))
        first, second = inventory["runs"]
        self.assertEqual(first["places"]["shim_path"], str(shim))
        self.assertEqual(second["places"]["shim_path"], str(moved))
        self.assertEqual(inventory["shim_path"], str(moved))
        args = type("Args", (), {"output": self.out})
        self.assertEqual(self.quiet(m.replay, args), 2)

    def test_resume_with_every_place_changed_keeps_the_kept_cells(self):
        self.patched()
        self.run_cells(CELLS[:1])
        stub, _ = make_stub(self.sb)

        class Elsewhere(stub):
            def __init__(self, args):
                super().__init__(args)
                self.header.update(
                    shim_path="/n/bracket.so", aliases=["/n/lib.alias"],
                    library="/elsewhr/libpolyml.so.16.0.0",
                    tmpdir=self.header["tmpdir"][:-2] + "s2")
        with mock.patch.object(m, "Grid", Elsewhere):
            self.quiet(m.run, arguments(self.out, CELLS[:1], resume=True))
        inventory = a.load(self.out / "inventory.json")
        self.assertEqual(inventory["library"],
                         "/elsewhr/libpolyml.so.16.0.0")
        self.assertEqual(inventory["runs"][0]["places"]["library"], tb.LIB)
        self.assertEqual(self.quiet(
            m.replay, type("Args", (), {"output": self.out})), 2)

    def test_resume_at_places_of_another_path_length_is_refused(self):
        self.patched()
        self.run_cells(CELLS[:1])
        before = (self.out / "inventory.json").read_bytes()
        stub, _ = make_stub(self.sb)
        for key, value in (("tmpdir", "/a-longer-scratch-directory"),
                           ("library", "/n/libpolyml.so.16.0.0")):
            class Elsewhere(stub):
                def __init__(self, args, key=key, value=value):
                    super().__init__(args)
                    self.header[key] = value
            with self.subTest(key), mock.patch.object(m, "Grid", Elsewhere):
                with self.assertRaisesRegex(
                        sc.InvalidAllocation,
                        "resume with different settings: %s-length$" % key):
                    self.quiet(m.run, arguments(self.out, CELLS[:2],
                                                resume=True))
        self.assertEqual((self.out / "inventory.json").read_bytes(), before)

    def test_resume_replays_the_kept_cells_first(self):
        self.patched()
        self.run_cells(CELLS[:1])
        archive = self.out / (CELLS[0] + ".json.xz")
        archive.write_bytes(archive.read_bytes() + b"x")
        log = self.patched()
        with self.assertRaisesRegex(sc.InvalidAllocation, "archive"):
            self.quiet(m.run, arguments(self.out, CELLS[:2], resume=True))
        self.assertEqual(log["cells"], [])  # refused before measuring

    def test_a_complete_run_cannot_be_resumed(self):
        self.patched()
        self.run_cells(CELLS[:1])
        (self.out / "decisions.json").write_text("{}")
        with self.assertRaisesRegex(sc.InvalidAllocation, "complete"):
            self.quiet(m.run, arguments(self.out, CELLS[:2], resume=True))

    def test_an_error_cancels_queued_cells_and_keeps_the_checkpoint(self):
        log = self.patched(boom=lambda case, size: size == 100, delay=0.3)
        with self.assertRaisesRegex(RuntimeError, "exploded"):
            self.run_cells(CELLS, jobs=1)
        # the failing cell, and at most the one the worker had already begun
        self.assertLessEqual(len(log["cells"]), 2)
        self.assertEqual(a.load(self.out / "inventory.json")["runs"], [])
        self.assertEqual(log["exits"], [RuntimeError])

    def test_an_interrupt_in_the_main_thread_also_cancels(self):
        log = self.patched(delay=0.3)

        def interrupted(futures, return_when):
            raise KeyboardInterrupt
        with mock.patch.object(m, "wait", interrupted):
            with self.assertRaises(KeyboardInterrupt):
                self.run_cells(CELLS, jobs=1)
        self.assertLessEqual(len(log["cells"]), 2)


class Replay(Bed):
    def test_a_complete_run_replays_against_its_final_files(self):
        decisions = dict(status="pass", complete=True)
        self.out.mkdir()
        a.save(self.out / "inventory.json", dict(runs=[]))
        a.save(self.out / "decisions.json", decisions)
        (self.out / "RESULTS.md").write_text("table\n")
        args = argparse.Namespace(output=self.out)
        with mock.patch.object(m, "finish", lambda root, inv: decisions), \
                mock.patch.object(m, "results_markdown",
                                  lambda found, label: "table\n"):
            self.assertEqual(self.quiet(m.replay, args), 0)
            (self.out / "RESULTS.md").write_text("other\n")
            with self.assertRaisesRegex(sc.InvalidAllocation, "results"):
                self.quiet(m.replay, args)


class CheckJobs(Bed):
    def check(self, cells, **kw):
        args = arguments(self.out, cells=cells, **kw)
        return self.quiet(m.check_jobs, args)

    def test_identical_counts_serial_and_parallel(self):
        self.patched()
        self.assertEqual(self.check(CELLS[:2], jobs=2), 0)
        report = a.load(self.out / "jobs-check.json")
        self.assertEqual((report["identical"], report["workers"]),
                         (True, {"serial": 1, "parallel": 2}))

    def test_a_parallel_only_difference_is_reported(self):
        def change(grid, experiment, side, pair):
            if grid.args.jobs > 1 and side == "candidate":
                return dict(work={"apply": {"native": 4}})
        self.patched(change=change)
        self.assertEqual(self.check(CELLS[:2], jobs=2), 2)
        self.assertFalse(a.load(self.out / "jobs-check.json")["identical"])

    def test_needs_two_distinct_cells_and_more_than_one_job(self):
        self.patched()
        for cells, jobs in (([CELLS[0]], 2), ([CELLS[0], CELLS[0]], 2),
                            (CELLS[:2], 1)):
            with self.subTest(cells=cells, jobs=jobs):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "two distinct cells"):
                    self.check(cells, jobs=jobs)
                self.assertFalse(self.out.exists())

    def test_a_parallel_run_that_used_one_worker_is_rejected(self):
        self.patched()
        real = m.run

        def single(args):
            code = real(args)
            path = args.output / "inventory.json"
            inventory = a.load(path)
            path.unlink()
            a.save(path, dict(inventory, jobs=[1]))
            return code
        with mock.patch.object(m, "run", single):
            with self.assertRaisesRegex(sc.InvalidAllocation, "workers"):
                self.check(CELLS[:2], jobs=2)

    def test_a_serial_run_that_used_several_workers_is_rejected(self):
        self.patched()
        real = m.run

        def several(args):
            code = real(args)
            path = args.output / "inventory.json"
            inventory = a.load(path)
            path.unlink()
            a.save(path, dict(inventory, jobs=[args.jobs + 1]))
            return code
        with mock.patch.object(m, "run", several):
            with self.assertRaisesRegex(sc.InvalidAllocation, "workers"):
                self.check(CELLS[:2], jobs=2)


class Process(Bed):
    """The real Grid.process around a fake launcher that replays stdout."""

    def setUp(self):
        super().setUp()
        self.grid = REAL.__new__(REAL)
        self.grid.args = arguments(self.out, timeout=60)
        self.grid.fds = ()
        self.grid.hol = self.sb.repo
        self.grid.lib = Path(tb.LIB)
        self.grid.aliases = [tb.ALIAS]
        self.grid.shim = self.sb.shim
        self.grid.run_env = dict(self.sb.base_environment(),
                                 LD_LIBRARY_PATH=str(Path(tb.LIB).parent))
        self.job = self.sb.job()
        self.job.sources = {str(f.resolve()): m.rp.fingerprint(f)
                            for d in self.job.dirs.values()
                            for f in d.iterdir()}

    def launcher(self, side, stdout, code=0):
        text = self.root / ("stdout-" + side)
        text.write_text(stdout)
        exe = self.job.dirs[side] / "paired.exe"
        exe.write_text("#!/bin/sh\ncat %s\nexit %d\n" % (text, code))
        exe.chmod(exe.stat().st_mode | stat.S_IXUSR)

    def process(self, side="candidate", pair=1, stdout=None, code=0, **kw):
        experiment = "candidate" if side != "control" else "control"
        good = self.sb.receipt(experiment, side, pair, 0, **kw)
        self.launcher(side, good["stdout"] if stdout is None else stdout,
                      code)
        return experiment, self.grid.process(
            self.job, experiment, side, CASE, 0, pair, tb.STEADY, tb.REPEATS)

    def test_a_valid_process_is_accepted_and_replays(self):
        for side in m.SIDES:
            with self.subTest(side):
                experiment, receipt = self.process(side)
                self.assertTrue(receipt["accepted"], receipt.get(
                    "rejection"))
                self.assertEqual((receipt["side"], receipt["selection"]),
                                 (side, m.SIDES[side]))
                receipt["position"] = 0 if side != "baseline" else 1
                receipt["pair"] = 1
                meta = dict(self.sb.bind(), schema=m.SCHEMA)
                if side == "baseline":
                    experiment = "candidate"
                obs = m.check_receipt(receipt, meta, experiment)
                self.assertEqual(obs["steady"], tb.STEADY)
                self.assertEqual(sorted(receipt["environment"]),
                                 sorted(self.sb.environment(side)))

    def test_protocol_violations_are_rejections_with_a_reason(self):
        good = self.sb.receipt("candidate", "candidate", 1, 0)["stdout"]
        cases = {
            "dead counter": (self.sb.receipt(
                "candidate", "candidate", 1, 0, work={
                    n: {} for n in sc.names(3)}, start=1)["stdout"], 0,
                "canary"),
            "wrong runtime": (good.replace(tb.LIB, "/usr/lib/libpolyml.so"),
                              0, "runtime"),
            "bad exit": (good, 1, "exit"),
            "malformed field": (good.replace("alloc.setup\t0;",
                                             "alloc.setup\tx;", 1), 0, ""),
            "no output": ("", 0, ""),
        }
        for label, (stdout, code, message) in cases.items():
            with self.subTest(label):
                _, receipt = self.process(stdout=stdout, code=code)
                self.assertFalse(receipt["accepted"])
                self.assertIn(message, receipt["rejection"])

    def test_a_file_error_while_validating_is_a_rejection(self):
        with mock.patch.object(m.rp, "validate",
                               side_effect=OSError("vanished")):
            _, receipt = self.process()
        self.assertEqual((receipt["accepted"], receipt["rejection"]),
                         (False, "vanished"))

    def test_a_malformed_bracket_field_is_a_rejection_not_a_crash(self):
        good = self.sb.receipt("candidate", "candidate", 1, 0)["stdout"]
        bad = good.replace("alloc.setup\t0;", "alloc.setup\t0;1,2;", 1)
        _, receipt = self.process(stdout=bad)
        self.assertFalse(receipt["accepted"])


class Resealing(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        for name in ("lib.so", "libc.so", "shim.so", "input", "tool",
                     "source", "hol.sml", "sigobj.sig"):
            (root / name).write_text(name + "\n")
        self.root = root
        # inputs are keyed relative to the harness checkout
        patch = mock.patch.object(m, "ROOT", root)
        patch.start()
        self.addCleanup(patch.stop)
        self.ldd = {"hol": "\t%s (0x1)\n\t%s (0x2)\n" % (
            root / "lib.so", root / "libc.so"),
            "shim": "\t%s (0x1)\n" % (root / "lib.so")}

        def run(command, cwd=None, runtime_env=None):
            key = "hol" if command[1].endswith("hol") else "shim"
            return dict(exit=0, timed_out=False, stdout=self.ldd[key])
        grid = REAL.__new__(REAL)
        grid.run = run
        grid.hol = root
        grid.run_env = {}
        grid.lib, grid.shim = root / "lib.so", root / "shim.so"
        grid.inputs = {"input": a.seal(root / "input")}
        grid.tools = {str(root / "tool"): a.seal(root / "tool")}
        grid.source_seals = {str(root / "source"): a.seal(root / "source")}
        grid.toolchain_seals = {str(root / n): a.seal(root / n)
                                for n in ("hol.sml", "sigobj.sig")}
        grid.libraries = loading.library_inputs(run(["ldd", "hol"]))
        grid.report = dict(
            runtime=a.seal(grid.lib), shim=a.seal(grid.shim),
            shim_libraries=loading.library_inputs(run(["ldd", "shim"])))
        self.grid = grid

    def test_untouched_grid_reseals(self):
        self.grid.reseal()

    def test_every_sealed_thing_is_checked_again(self):
        def write(name):
            return lambda: (self.root / name).write_text("changed\n")

        def ldd(key):
            def change():
                self.ldd[key] += "\t%s (0x3)\n" % (self.root / "tool")
            return change
        cases = (("input", write("input"), "sealed input changed"),
                 ("tool", write("tool"), "sealed input changed"),
                 ("source", write("source"), "sealed input changed"),
                 ("toolchain source", write("hol.sml"),
                  "sealed input changed"),
                 ("sigobj", write("sigobj.sig"), "sealed input changed"),
                 ("runtime", write("lib.so"), "runtime changed"),
                 ("shim", write("shim.so"), "shim changed"),
                 ("ordinary library", write("libc.so"), "linkage drift"),
                 ("hol linkage", ldd("hol"), "instrumented linkage drift"),
                 ("shim linkage", ldd("shim"), "shim linkage drift"))
        for label, change, message in cases:
            with self.subTest(label):
                self.setUp()
                change()
                with self.assertRaisesRegex(FAILURES, message):
                    self.grid.reseal()

    def test_exit_reseals_only_a_prepared_clean_run(self):
        calls = []
        locks = []

        class Lock:
            def __exit__(self, *exc):
                locks.append(exc[0])
        self.grid._lock = Lock()
        self.grid.scratch = self.root / "scratch"
        self.grid.scratch.mkdir()
        self.grid.reseal = lambda: calls.append("reseal")
        self.grid.ready = False
        self.assertFalse(self.grid.__exit__(None, None, None))
        self.assertEqual(calls, [])
        self.grid.scratch.mkdir()
        self.grid.ready = True
        self.grid.__exit__(RuntimeError, RuntimeError("x"), None)
        self.assertEqual(calls, [])
        self.grid.scratch.mkdir()
        self.grid.__exit__(None, None, None)
        self.assertEqual(calls, ["reseal"])
        self.assertEqual(locks, [None, None, None])
        self.assertFalse(self.grid.scratch.exists())

    def test_failed_reseal_still_releases_the_lock_and_scratch(self):
        locks = []

        class Lock:
            def __exit__(self, *exc):
                locks.append(1)
        self.grid._lock = Lock()
        self.grid.scratch = self.root / "scratch"
        self.grid.scratch.mkdir()
        self.grid.ready = True
        (self.root / "input").write_text("changed\n")
        with self.assertRaises(FAILURES):
            self.grid.__exit__(None, None, None)
        self.assertEqual(locks, [1])
        self.assertFalse(self.grid.scratch.exists())


class Preparation(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def grid(self, **kw):
        values = dict(
            baseline=tb.BASE_PIN, candidate=tb.CAND_PIN,
            toolchain=self.root / "tc", repo=self.root, timeout=60,
            authorize_experimental_runtime=True, pairs=2, jobs=2,
            controls_receipt=self.root / "controls.json",
            output=self.root / "out", source=self.root / "src")
        values.update(kw)
        return REAL(argparse.Namespace(**values))

    def test_vacuous_comparison_is_refused(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "vacuous"):
            self.grid(candidate=tb.BASE_PIN).__enter__()

    def test_exact_pins_authorization_and_timeout_are_required(self):
        for kw in (dict(candidate="HEAD"), dict(baseline="main"),
                   dict(authorize_experimental_runtime=False),
                   dict(timeout=0)):
            with self.subTest(kw):
                with self.assertRaises(ValueError):
                    self.grid(**kw).__enter__()

    def test_only_a_successful_toolchain_at_the_candidate_is_admitted(self):
        (self.root / "tc").mkdir()
        good = dict(schema="task29b-toolchain-v1", success=True,
                    head=tb.CAND_PIN, lineage={})
        for label, lineage in (
                ("failed", dict(good, success=False)),
                ("no success flag", {k: v for k, v in good.items()
                                     if k != "success"}),
                ("truthy only", dict(good, success=1)),
                ("other head", dict(good, head=tb.BASE_PIN)),
                ("other schema", dict(good, schema="task29b-toolchain-v0"))):
            with self.subTest(label):
                (self.root / "tc/lineage.json").write_text(
                    json.dumps(lineage))
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "not built at the candidate"):
                    self.grid().prepare()

    def built(self, **change):
        """A toolchain lineage and the files it seals under hol-source."""
        hol = self.root / "tc/hol-source"
        (hol / "sigobj").mkdir(parents=True, exist_ok=True)
        for name in ("src/A.sml", "src/B.sml", "sigobj/A.sig"):
            (hol / name).parent.mkdir(parents=True, exist_ok=True)
            (hol / name).write_text(name + "\n")
        built = dict(
            hol_snapshot=tb.CAND_PIN, native_configuration="config\n",
            hol_source_inputs={n: a.seal(hol / n)
                               for n in ("src/A.sml", "src/B.sml")},
            hol_source_changes={},
            hol_sigobj={"sigobj/A.sig": a.seal(hol / "sigobj/A.sig")})
        built.update(change)
        return hol, {k: v for k, v in built.items() if v is not ...}

    def sources(self, built):
        grid = self.grid()
        grid.hol = self.root / "tc/hol-source"
        return grid.check_toolchain_sources(built)

    def test_toolchain_sources_and_sigobj_are_sealed_at_the_start(self):
        hol, built = self.built()
        seals = self.sources(built)
        self.assertEqual(sorted(seals), sorted(
            str(hol / n) for n in ("src/A.sml", "src/B.sml",
                                   "sigobj/A.sig")))
        for name in ("src/A.sml", "src/B.sml", "sigobj/A.sig"):
            with self.subTest(name):
                path = hol / name
                text = path.read_text()
                path.write_text("changed\n")
                with self.assertRaisesRegex(ValueError,
                                            "sealed input changed"):
                    self.sources(built)
                path.write_text(text)

    def test_a_source_the_build_itself_rewrote_is_sealed_as_rewritten(self):
        hol, built = self.built()
        (hol / "src/B.sml").write_text("as the build left it\n")
        with self.assertRaisesRegex(ValueError, "sealed input changed"):
            self.sources(built)
        built["hol_source_changes"] = {
            "src/B.sml": a.seal(hol / "src/B.sml")}
        self.assertIn(str(hol / "src/B.sml"), self.sources(built))

    def test_a_lineage_of_another_snapshot_or_without_seals_is_refused(self):
        for label, change, message in (
                ("other snapshot", dict(hol_snapshot=tb.BASE_PIN),
                 "not that of the candidate"),
                ("no snapshot", dict(hol_snapshot=...), "rebuild"),
                ("no sources", dict(hol_source_inputs=...), "rebuild"),
                ("no changes", dict(hol_source_changes=...), "rebuild"),
                ("no sigobj", dict(hol_sigobj=...), "rebuild"),
                ("sigobj not a mapping", dict(hol_sigobj=[]), "rebuild"),
                ("nothing sealed", dict(hol_source_inputs={},
                                        hol_sigobj={}),
                 "not that of the candidate")):
            with self.subTest(label):
                _, built = self.built(**change)
                with self.assertRaisesRegex(sc.InvalidAllocation, message):
                    self.sources(built)

    def prepared(self, **patches):
        """prepare() up to the first thing that builds, with the toolchain
        accepted and the later steps recorded."""
        (self.root / "tc").mkdir(exist_ok=True)
        (self.root / "tc/lineage.json").write_text(json.dumps(dict(
            schema="task29b-toolchain-v1", success=True, head=tb.CAND_PIN,
            lineage=dict(native_configuration="config\n", hol_products={},
                         native_products={}))))
        later = []
        grid = self.last = self.grid()
        self.addCleanup(self.closed, grid)
        steps = dict(
            check_toolchain_sources=lambda built: {},
            checkout=lambda *args: later.append("checkout") or 1 / 0)
        steps.update(patches)
        with mock.patch.object(m.pr, "reject_compact32"), \
                mock.patch.object(m.pr, "verify_source",
                                  side_effect=lambda *a: later.append(
                                      "verify_source")), \
                mock.patch.object(m.pr, "build_runtime",
                                  side_effect=lambda *a: later.append(
                                      "build_runtime")):
            for name, value in steps.items():
                setattr(grid, name, value)
            try:
                grid.prepare()
            except Exception as error:
                return error, later
        raise AssertionError("prepare did not stop")

    def test_the_environment_is_fixed_and_the_inputs_are_relative(self):
        sealed = []

        def seal_tools(env, run):
            sealed.append(dict(env))
            return {"/usr/bin/tool": dict(sha256="t" * 64, bytes=1)}
        self.addCleanup(shutil.rmtree, self.root / "tmp", True)
        with mock.patch.dict(os.environ, PATH="/elsewhere:/bin",
                             TMPDIR=str(self.root / "tmp")), \
                mock.patch.object(m.bd, "resolve", return_value={}), \
                mock.patch.object(m, "harness_binding", return_value={}), \
                mock.patch.object(m.pr, "seal_tools", seal_tools):
            (self.root / "tmp").mkdir()
            hol = self.root / "tc/hol-source"
            (hol / "bin").mkdir(parents=True)
            for name in ("bin/hol.state.min", "holproject.toml"):
                (hol / name).write_text(name + "\n")
            error, later = self.prepared()
        self.assertIsInstance(error, ZeroDivisionError)
        grid = self.last
        # not the caller's PATH, and the tools it resolves to are sealed
        self.assertEqual(grid.env["PATH"], m.pr.PATH)
        self.assertEqual(sealed, [grid.env])
        self.assertIn("/usr/bin/tool", grid.tools)
        self.assertEqual(grid.env["TMPDIR"], str(self.root / "tmp"))
        self.assertEqual(grid.env["CC"], shutil.which(
            "gcc", path=m.pr.PATH))
        # keyed by path relative to the harness checkout
        files, _ = m.harness_files()
        self.assertEqual(sorted(grid.inputs), sorted(
            p.relative_to(m.ROOT).as_posix() for p in files))
        for name in grid.inputs:
            self.assertFalse(Path(name).is_absolute(), name)
            self.assertTrue((m.ROOT / name).is_file(), name)

    def test_the_driver_path_is_a_constant_of_system_directories(self):
        self.assertEqual(m.pr.PATH.split(":"),
                         ["/usr/local/bin", "/usr/bin", "/bin"])

    def closed(self, grid):
        if getattr(grid, "scratch", None):
            shutil.rmtree(grid.scratch, ignore_errors=True)

    def test_an_unreviewed_difference_is_refused_before_any_build(self):
        refusal = sc.InvalidAllocation("boundary: differences outside")
        with mock.patch.object(m.bd, "resolve", side_effect=refusal), \
                mock.patch.object(m, "harness_binding",
                                  side_effect=AssertionError("too early")):
            error, later = self.prepared()
        self.assertIs(error, refusal)
        self.assertEqual(later, [])

    def test_the_boundary_is_resolved_for_this_pair_and_sequence(self):
        resolved = []

        def resolve(*args):
            resolved.append(args)
            raise sc.InvalidAllocation("stop here")
        with mock.patch.object(m.bd, "resolve", resolve):
            self.prepared()
        self.assertEqual(resolved, [(self.root, tb.BASE_PIN, tb.CAND_PIN,
                                     m.pr.HOL_SEQUENCE, m.BOUNDARY)])

    def test_a_harness_that_is_not_its_commit_is_refused_before_any_build(
            self):
        refusal = sc.InvalidAllocation("harness input differs")
        with mock.patch.object(m.bd, "resolve", return_value={}), \
                mock.patch.object(m, "harness_binding",
                                  side_effect=refusal) as bound:
            error, later = self.prepared()
        self.assertIs(error, refusal)
        self.assertEqual(later, [])
        root, candidate, inputs, fixtures = bound.call_args[0]
        self.assertEqual((Path(root), candidate),
                         (m.HERE.parents[3], tb.CAND_PIN))
        names = {Path(p).name for p in inputs}
        self.assertTrue({"allocation_matrix.py", "allocation_boundary.json",
                         "path_schema.py", "MatrixSupport.sml",
                         "run_paired.py", "bracket.c"} <= names)
        self.assertEqual({Path(p).name for p in fixtures} & {
            "MatrixAllocation.sml", "MatrixSupport.sml"},
            {"MatrixAllocation.sml", "MatrixSupport.sml"})

    def test_a_toolchain_that_changed_is_refused_before_any_build(self):
        refusal = sc.InvalidAllocation("sealed input changed: x")
        error, later = self.prepared(
            check_toolchain_sources=mock.Mock(side_effect=refusal))
        self.assertIs(error, refusal)
        self.assertEqual(later, [])

    def test_only_a_linux_aarch64_host_is_accepted(self):
        for system, machine in (("darwin", "aarch64"), ("linux", "x86_64")):
            with self.subTest(system=system, machine=machine):
                with mock.patch.object(m.sys, "platform", system), \
                        mock.patch.object(m.platform, "machine",
                                          return_value=machine):
                    with self.assertRaisesRegex(sc.InvalidAllocation,
                                                "unsupported host"):
                        self.grid().__enter__()

    def test_prepare_failure_is_not_masked_and_releases_the_lock(self):
        released = []

        @contextlib.contextmanager
        def lock(repo):
            try:
                yield ()
            finally:
                released.append(repo)
        grid = self.grid()
        with mock.patch.object(m.a, "serial_lock", lock), \
                mock.patch.object(m.platform, "machine",
                                  return_value="aarch64"), \
                mock.patch.object(m.sys, "platform", "linux"), \
                mock.patch.object(REAL, "prepare",
                                  side_effect=RuntimeError("boom")):
            with self.assertRaisesRegex(RuntimeError, "boom"):
                grid.__enter__()
        self.assertEqual(len(released), 1)


class Controls(unittest.TestCase):
    RUNTIME = tb.RUNTIME

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def receipt(self, **change):
        return tb.controls_data(**change)

    def write(self, data, name="controls.json"):
        path = self.root / name
        if name.endswith(".gz"):
            path.write_bytes(gzip.compress(json.dumps(data).encode()))
        else:
            path.write_text(json.dumps(data))
        return path

    def accept(self, data, runtime=None, tree=TREE, libraries=None,
               configuration="config\n"):
        return m.controls_receipt(
            self.write(data), dict(runtime or self.RUNTIME), tree,
            libraries or tb.toolchain_libraries(), configuration)

    def resealed(self, program, text):
        """The receipt with the text of one path launcher's output replaced
        and its seal recomputed: only the schema can refuse it."""
        data = self.receipt()
        for row in data["commands"]:
            if Path(row["command"][0]).name == program:
                raw = text.encode()
                row.update(stdout=text, stdout_bytes=len(raw),
                           stdout_sha256=hashlib.sha256(raw).hexdigest())
        return data

    def test_a_receipt_for_this_runtime_is_accepted_plain_or_gzipped(self):
        for name in ("controls.json", "controls.json.gz"):
            with self.subTest(name):
                path = self.write(self.receipt(), name)
                found = m.controls_receipt(
                    path, dict(self.RUNTIME), TREE, tb.toolchain_libraries(),
                    "config\n")
                self.assertEqual(found, dict(
                    receipt=a.seal(path), runtime=self.RUNTIME,
                    head=tb.CAND_PIN, tree=TREE,
                    native_configuration=hashlib.sha256(
                        b"config\n").hexdigest(),
                    libraries=m.library_names(tb.toolchain_libraries()),
                    file="controls-receipt." + name.split(".", 1)[1]))

    def test_every_other_receipt_is_refused(self):
        other = dict(sha256="s" * 64, bytes=7)
        cases = (
            ("schema", self.receipt(schema="task29-other-v3"),
             "not a successful"),
            ("failed", self.receipt(success=False), "not a successful"),
            ("truthy", self.receipt(success=1), "not a successful"),
            ("failure text", self.receipt(failure="x"), "not a successful"),
            ("other runtime sha", self.receipt(runtime=other),
             "different runtime"),
            ("other runtime size", self.receipt(
                runtime=dict(self.RUNTIME, bytes=8)), "different runtime"),
            ("no runtime", self.receipt(runtime=...), "malformed"),
            ("no inputs", self.receipt(inputs=...), "malformed"),
            ("no head", self.receipt(head=...), "malformed"),
            ("no success", self.receipt(success=...), "malformed"),
            ("runtime not a mapping", self.receipt(runtime=None),
             "different runtime"),
            ("inputs not a mapping", self.receipt(inputs=[]), "malformed"),
            ("no harness", self.receipt(harness=...), "malformed"),
            ("no lineage", self.receipt(lineage=...), "malformed"),
            ("dirty harness", self.receipt(harness=harness(dirty=True)),
             "clean, committed harness"),
            ("dirty not a bool", self.receipt(harness=harness(dirty=0)),
             "clean, committed harness"),
            ("harness at another head", self.receipt(
                harness=harness(head="9" * 40)), "clean, committed harness"),
            ("other tree outside performance", self.receipt(
                harness=harness(tree_outside_performance="f" * 64)),
             "differs from the candidate"),
            ("lineage of another head", self.receipt(
                lineage=lineage(hol_snapshot="9" * 40)), "no HOL lineage"),
            ("lineage without HOL products", self.receipt(
                lineage=lineage(hol_products={})), "no HOL lineage"),
            ("lineage without native products", self.receipt(
                lineage=lineage(native_products={})), "no HOL lineage"),
            ("lineage without configuration", self.receipt(
                lineage=lineage(native_configuration=...)), "malformed"),
            ("no libraries", self.receipt(instrumented_libraries=...),
             "malformed"),
            ("empty lineage", self.receipt(lineage={}), "malformed"))
        for label, data, message in cases:
            with self.subTest(label):
                with self.assertRaisesRegex(sc.InvalidAllocation, message):
                    self.accept(data)

    def test_the_receipt_must_come_from_the_toolchains_own_build(self):
        libraries = tb.toolchain_libraries()
        other = dict(libraries, **{"/usr/lib/libc.so.6": dict(
            resolved="/o", sha256="e" * 64, bytes=3)})
        fewer = {k: v for k, v in libraries.items() if "polyml" in k}
        for label, change, message in (
                ("other library seal", dict(libraries=other),
                 "other instrumented libraries"),
                ("missing library", dict(libraries=fewer),
                 "other instrumented libraries"),
                ("other configuration", dict(configuration="other\n"),
                 "another native Poly/ML configuration")):
            with self.subTest(label):
                with self.assertRaisesRegex(sc.InvalidAllocation, message):
                    self.accept(self.receipt(), **change)
        # The raw paths of the build need not agree, only name and seal.
        moved = {"/another/place/" + Path(k).name: v
                 for k, v in libraries.items()}
        self.accept(self.receipt(), libraries=moved)

    def test_every_harness_file_must_be_the_one_of_this_checkout(self):
        names = [p for p in m.pr.harness_inputs()]
        self.assertIn("run_controls.py", [p.name for p in names])
        self.assertIn("private_runtime.py", [p.name for p in names])
        self.assertIn("bracket.c", [p.name for p in names])
        for path in names:
            key = str(path)
            with self.subTest(path.name):
                data = self.receipt()
                data["inputs"][key] = dict(sha256="0" * 64, bytes=1)
                with self.assertRaisesRegex(sc.InvalidAllocation, path.name):
                    self.accept(data)
                del data["inputs"][key]
                with self.assertRaisesRegex(sc.InvalidAllocation, path.name):
                    self.accept(data)

    def test_harness_files_are_known_by_directory_and_name(self):
        data = self.receipt()
        data["inputs"] = {k.replace("allocator-counter", "elsewhere"): v
                          for k, v in data["inputs"].items()}
        with self.assertRaisesRegex(sc.InvalidAllocation, "different"):
            self.accept(data)

    def test_an_older_weaker_path_receipt_no_longer_passes(self):
        label = guards.s.labels(guards.INTERP)[1]

        def reserved(fields):
            fields[-1] = "1"
        text = guards.tamper(guards.INTERP, "BENDPOINT", label, reserved,
                             "end")
        data = self.resealed("interpreter-path-controls.exe", text)
        with self.assertRaisesRegex(
                sc.InvalidAllocation,
                r"fails the current path schema \(interpreter-path.*"
                "branch ABI/overflow/reserved mismatch"):
            self.accept(data)

    def test_path_observations_are_those_of_a_replay(self):
        for key in ("path", "interpreter_path", "failure_path"):
            with self.subTest(key):
                data = self.receipt()
                data[key + "_observations"] = {"x": 1}
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "differ from a replay"):
                    self.accept(data)
                del data[key + "_observations"]
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "malformed"):
                    self.accept(data)

    def test_each_path_process_must_be_present_once(self):
        for program in ("path-controls.exe", "interpreter-path-controls.exe",
                        "failure-path-controls.exe"):
            with self.subTest(program):
                data = self.receipt()
                rows = data["commands"]
                kept = [c for c in rows
                        if Path(c["command"][0]).name != program]
                data["commands"] = kept
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "lacks the " + program):
                    self.accept(data)
                data["commands"] = rows + [c for c in rows
                                           if c not in kept]
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "lacks the " + program):
                    self.accept(data)

    def test_a_path_process_that_failed_is_refused(self):
        data = self.receipt()
        data["commands"][0]["exit"] = 1
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "current path schema"):
            self.accept(data)

    def test_missing_receipt_file_is_an_error(self):
        with self.assertRaises(FileNotFoundError):
            m.controls_receipt(self.root / "none.json", self.RUNTIME, TREE,
                               tb.toolchain_libraries(), "config\n")


class Lineage(unittest.TestCase):
    """What build_native_hol records, over a fake runner and a throwaway
    repository: no compiler is built and no HOL is compiled."""

    def setUp(self):
        import bootstrap_probe
        import private_runtime
        self.probe, self.pr = bootstrap_probe, private_runtime
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "repo"
        (self.repo / "tools-poly").mkdir(parents=True)
        (self.repo / "tools-poly/Other.ML").write_text("x\n")
        (self.repo / "tracked.sml").write_text("val x = 1\n")
        for command in (["init", "-q"], ["add", "-A"], [
                "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q",
                "-m", "m"]):
            subprocess.run(["git", "-C", str(self.repo), *command],
                           check=True, stdout=subprocess.PIPE)
        self.pristine = self.root / "pristine"
        self.pristine.mkdir()
        (self.pristine / "configure").write_text("#!/bin/sh\n")
        (self.root / "SOURCE_SHA256.json").write_text('{"files": {}}')
        self.commands = []

    def run_one(self, command, cwd=None):
        self.commands.append(list(command))
        out = dict(exit=0, timed_out=False, stdout="")
        name = Path(command[0]).name
        dst = self.root / "dst"
        if name == "configure":
            (dst / "native-source/config.log").write_text("log\n")
            (dst / "native-source/config.h").write_text("config\n")
        elif command[:2] == ["make", "install"]:
            (dst / "native-install/bin").mkdir(parents=True)
            (dst / "native-install/bin/poly").write_text("poly\n")
        elif name == "build":
            hol = dst / "hol-source"
            (hol / "bin").mkdir(exist_ok=True)
            for product in ("hol", "hol.state0", "Holmake"):
                (hol / "bin" / product).write_text(product + "\n")
            (hol / "sigobj").mkdir()
            (hol / "sigobj/A.sig").write_text("sig A\n")
            (hol / "sigobj/A.uo").write_text("uo A\n")
            (hol / "sigobj/dir").mkdir()
        elif name == "ldd":
            out["stdout"] = "\t%s (0x1)\n" % (self.root / "SOURCE_SHA256.json")
        elif name == "git":
            subprocess.run(command, cwd=cwd, check=True,
                           stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return out

    def build(self):
        (self.root / "dst").mkdir()
        report = {}
        with mock.patch.object(self.pr, "verify_source"), \
                mock.patch.object(self.probe, "HERE", self.root), \
                mock.patch.object(self.probe, "bootstrap_stages",
                                  return_value=[]):
            hol = self.probe.build_native_hol(
                self.pristine, self.root / "dst", self.repo, {},
                self.run_one, report)
        return hol, report

    def test_sigobj_and_sources_are_sealed_as_the_build_left_them(self):
        hol, report = self.build()
        self.assertEqual(report["hol_sigobj"], {
            "sigobj/A.sig": a.seal(hol / "sigobj/A.sig"),
            "sigobj/A.uo": a.seal(hol / "sigobj/A.uo")})
        self.assertEqual(report["hol_snapshot"], a.git(
            self.repo, "rev-parse", "HEAD"))
        self.assertEqual(sorted(report["hol_source_inputs"]),
                         ["tools-poly/Other.ML", "tracked.sml"])
        # the one file the build itself rewrote is the recorded change
        self.assertEqual(report["hol_source_changes"], {})
        self.assertEqual(report["native_configuration"], "config\n")
        self.assertEqual(sorted(Path(k).name
                                for k in report["hol_products"]),
                         ["Holmake", "hol", "hol.state0"])

    def test_the_build_runs_the_sequence_the_boundary_is_judged_by(self):
        self.build()
        build = [c for c in self.commands if Path(c[0]).name == "build"]
        self.assertEqual(len(build), 1)
        self.assertIn("--seq=" + self.pr.HOL_SEQUENCE, build[0])
        self.assertEqual(self.pr.HOL_SEQUENCE, "tools/sequences/upto-parallel")


class Toolchain(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "tc"
        import bootstrap_probe
        self.probe = bootstrap_probe

    @contextlib.contextmanager
    def environment(self, build, lock=None):
        @contextlib.contextmanager
        def free(repo):
            yield ()
        with mock.patch.object(self.probe, "build_native_hol", build), \
                mock.patch.object(m.a, "serial_lock", lock or free), \
                mock.patch.object(m.a, "git",
                                  lambda *args: tb.CAND_PIN), \
                mock.patch.object(m.platform, "machine",
                                  return_value="aarch64"), \
                contextlib.redirect_stdout(io.StringIO()):
            yield

    def args(self):
        return argparse.Namespace(
            toolchain=self.root, repo=m.HERE.parents[3], source=None,
            timeout=60)

    def test_success_records_the_lineage_with_a_success_flag(self):
        def build(source, dst, repo, env, run, lineage):
            lineage["native_configuration"] = "config"
        with self.environment(build):
            self.assertEqual(m.toolchain(self.args()), 0)
        found = a.load(self.root / "lineage.json")
        self.assertIs(found["success"], True)
        self.assertEqual(found["schema"], "task29b-toolchain-v1")
        self.assertEqual(found["lineage"], {"native_configuration": "config"})
        self.assertFalse((self.root / "lineage-failed.json").exists())

    def test_the_standalone_probe_runs_under_the_fixed_path(self):
        with mock.patch.dict(os.environ, PATH="/elsewhere:/bin"):
            with contextlib.redirect_stderr(io.StringIO()):
                with self.assertRaises(SystemExit):
                    self.probe.main(["--output", "/nonexistent/o.json"])
            self.assertEqual(os.environ["PATH"], m.pr.PATH)

    def test_the_toolchain_builds_under_the_drivers_fixed_path(self):
        seen = []

        def build(source, dst, repo, env, run, lineage):
            seen.append(dict(env))
        with mock.patch.dict(os.environ, PATH="/elsewhere:/bin"), \
                self.environment(build):
            m.toolchain(self.args())
        self.assertEqual(seen[0]["PATH"], m.pr.PATH)
        self.assertEqual(a.load(self.root / "lineage.json")[
            "environment"]["PATH"], m.pr.PATH)

    def test_failure_is_never_admitted_as_a_toolchain(self):
        def build(source, dst, repo, env, run, lineage):
            lineage["partial"] = True
            raise sc.InvalidAllocation("bootstrap broke")
        with self.environment(build):
            with self.assertRaisesRegex(sc.InvalidAllocation, "broke"):
                m.toolchain(self.args())
        self.assertFalse((self.root / "lineage.json").exists())
        found = a.load(self.root / "lineage-failed.json")
        self.assertIs(found["success"], False)
        self.assertEqual(found["lineage"], {"partial": True})
        with self.assertRaises(FileNotFoundError):
            REAL(argparse.Namespace(
                baseline=tb.BASE_PIN, candidate=tb.CAND_PIN, pairs=2,
                repo=m.HERE.parents[3], toolchain=self.root)).prepare()

    def test_a_missing_compiler_is_refused(self):
        with self.environment(lambda *args: None):
            with mock.patch.object(m.shutil, "which", return_value=None):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "missing compiler"):
                    m.toolchain(self.args())
        self.assertFalse(self.root.exists())

    def test_a_failing_build_command_stops_the_build(self):
        results = []

        def build(source, dst, repo, env, run, lineage):
            for change in ({}, dict(exit=1), dict(timed_out=True)):
                results.append(change)
                done = dict(dict(exit=0, timed_out=False, stdout="",
                                 command=["x"], cwd="."), **change)
                with mock.patch.object(m.loading, "execute",
                                       return_value=done):
                    run(["x"], Path("."))
        with self.environment(build):
            with self.assertRaisesRegex(sc.InvalidAllocation,
                                        "failed command"):
                m.toolchain(self.args())
        self.assertEqual(results, [{}, dict(exit=1)])
        found = a.load(self.root / "lineage-failed.json")
        self.assertIs(found["success"], False)
        self.assertEqual(len(found["commands"]), 2)

    def test_a_timed_out_build_command_stops_the_build(self):
        def build(source, dst, repo, env, run, lineage):
            done = dict(exit=0, timed_out=True, stdout="", command=["x"],
                        cwd=".")
            with mock.patch.object(m.loading, "execute", return_value=done):
                run(["x"], Path("."))
        with self.environment(build):
            with self.assertRaisesRegex(sc.InvalidAllocation,
                                        "failed command"):
                m.toolchain(self.args())

    def test_only_the_supported_host_builds_a_toolchain(self):
        with self.environment(lambda *args: None):
            with mock.patch.object(m.platform, "machine",
                                   return_value="x86_64"):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "unsupported host"):
                    m.toolchain(self.args())
        self.assertFalse(self.root.exists())

    def test_a_busy_lock_creates_nothing(self):
        @contextlib.contextmanager
        def busy(repo):
            raise a.Blocked("performance/build lock busy: x")
            yield ()
        with self.environment(lambda *args: None, busy):
            with self.assertRaises(a.Blocked):
                m.toolchain(self.args())
        self.assertFalse(self.root.exists())


class Command(unittest.TestCase):
    def setUp(self):
        # main() makes the fixed PATH the process environment: undo that.
        patcher = mock.patch.dict(os.environ)
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_every_entry_point_runs_under_the_fixed_path(self):
        base = ["--output", "/o", "--candidate", tb.CAND_PIN, "--toolchain",
                "/t", "--controls-receipt", "/c.json"]
        fake = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, fake)
        (fake / "git").write_text("#!/bin/sh\necho fake\n")
        (fake / "git").chmod(0o755)
        caller = "%s:%s" % (fake, os.environ["PATH"])
        for action, handler, extra in (
                ("run", "run", []), ("check-jobs", "check_jobs",
                                     ["--cells", "a-0", "b-0"]),
                ("replay", "replay", []), ("toolchain", "toolchain", [])):
            args = [action] + (["--output", "/o"] if action == "replay"
                               else ["--toolchain", "/t"] if
                               action == "toolchain" else base) + extra
            with self.subTest(action):
                os.environ["PATH"] = caller
                seen = []

                def entry(parsed):
                    seen.append((os.environ["PATH"], shutil.which("git")))
                    return 0
                with mock.patch.object(m, handler, entry):
                    m.main(args)
                self.assertEqual(seen, [(m.pr.PATH, shutil.which(
                    "git", path=m.pr.PATH))])
                self.assertNotEqual(seen[0][1], str(fake / "git"))
        # even a command line that is refused finds PATH already fixed
        os.environ["PATH"] = caller
        with contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit):
                m.main(["run"])
        self.assertEqual(os.environ["PATH"], m.pr.PATH)

    def test_controls_receipt_is_required_and_forwarded(self):
        base = ["--output", "/o", "--candidate", tb.CAND_PIN, "--toolchain",
                "/t"]
        for action in ("run", "check-jobs"):
            extra = ["--cells", "a-0", "b-0"] if action == "check-jobs" \
                else []
            with self.subTest(action):
                with contextlib.redirect_stderr(io.StringIO()):
                    with self.assertRaises(SystemExit):
                        m.main([action, *base, *extra])
                seen = []
                handler = {"run": "run", "check-jobs": "check_jobs"}[action]
                with mock.patch.object(m, handler,
                                       lambda args: seen.append(args) or 0):
                    # main() binds the function table at call time.
                    m.main([action, *base, *extra, "--controls-receipt",
                            "/c.json.gz"])
                self.assertEqual(seen[0].controls_receipt,
                                 Path("/c.json.gz"))

    def test_a_positive_job_count_is_required(self):
        argv = ["run", "--output", "/o", "--candidate", tb.CAND_PIN,
                "--toolchain", "/t", "--controls-receipt", "/c.json",
                "--jobs", "0"]
        with mock.patch.object(m, "run", lambda args: 0):
            with self.assertRaisesRegex(sc.InvalidAllocation, "positive"):
                m.main(argv)

    def test_more_jobs_than_two_digits_name_is_refused(self):
        base = ["--output", "/o", "--candidate", tb.CAND_PIN, "--toolchain",
                "/t", "--controls-receipt", "/c.json"]
        for action, handler, extra in (
                ("run", "run", []),
                ("check-jobs", "check_jobs", ["--cells", "a-0", "b-0"])):
            seen = []
            with self.subTest(action), mock.patch.object(
                    m, handler, lambda args: seen.append(args) or 0):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "--jobs above 100"):
                    m.main([action, *base, *extra, "--jobs", "101"])
                self.assertEqual(seen, [])
                m.main([action, *base, *extra, "--jobs", "100"])
                self.assertEqual(len(seen), 1)

    def test_fewer_than_an_ab_and_a_ba_pair_is_refused(self):
        argv = ["run", "--output", "/o", "--candidate", tb.CAND_PIN,
                "--toolchain", "/t", "--controls-receipt", "/c.json",
                "--pairs", "1"]
        seen = []
        with mock.patch.object(m, "run", lambda args: seen.append(args)):
            with self.assertRaisesRegex(sc.InvalidAllocation, "AB and a BA"):
                m.main(argv)
            m.main(argv[:-1] + ["2"])
        self.assertEqual(len(seen), 1)


if __name__ == "__main__":
    unittest.main()
