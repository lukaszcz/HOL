#!/usr/bin/env python3
"""The attempts and the pins the TASK31 disposition binds (task31_dispose.py),
against real engines and real ledgers (task31_followup.table, tg.Ledger, the
void rule of void_attempts.py), with nothing under test replaced."""
import argparse
from pathlib import Path
import tempfile
import unittest

import acceptance as a
import import_closure as ic
import task31_cases as c
import task31_dispose as d
import task31_followup as follow
import task31_grid as timing
import task31_pins as reviewed
import timing_grid as tg

CELLS = ["traversal_construct-0", "tactic_full_complete-100"]
SOURCE = "src/simp/src/Cond_rewr.sig"
OLD, OLD2 = "a" * 64, "b" * 64


def entry(path, blob="2" * 40, kind="source"):
    return dict(path=path, kind=kind, baseline_blob="1" * 40,
                candidate_blob=blob, reason="why", gate="gate 2")


def seal(digest):
    return dict(bytes=1, sha256=digest)


class World(unittest.TestCase):
    """A ledger, outputs and an engine."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="task31-attempts-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.ledger = self.root / "attempts.jsonl"
        self.follow = tg.Grid(follow.table(CELLS), doc="x")
        self.args = argparse.Namespace(repo=self.root, ledger=self.ledger)
        folder = self.root / "failed"
        folder.mkdir()
        a.save(folder / "acceptance.json", dict(success=False, commands=[]))
        self.archive = self.root / "failed.json.xz"
        self.files = tg.bundle.pack(folder, self.archive)

    def lines(self, engine, attempt, stage, output, *events, status=None):
        """The ledger lines of an attempt: open, resume and close events."""
        for event in events:
            more = dict(status=status) if event == "close" else {}
            tg.ledger_append(
                self.ledger, event=event, stage=stage, table=engine.t.name,
                attempt=attempt, candidate="c" * 40, output=str(output),
                checkout="x", **more)

    def output(self, engine, name, attempt, protocol=False, **more):
        """An output whose inventory has a row for every cell of the
        engine's table, each a protocol failure (or not) with the archive
        of a failed acceptance."""
        out = self.root / name
        out.mkdir()
        runs = [dict(case=case, size=size, protocol=protocol,
                     archive=self.archive.name, seal=a.seal(self.archive))
                for case, size in engine.t.keys()]
        (out / self.archive.name).write_bytes(self.archive.read_bytes())
        a.save(out / "inventory.json", dict(attempt=attempt, runs=runs,
                                            **more))
        return out

    def attempts(self, engine, judged):
        return d.attempts_of(self.args, engine, judged)


class FollowUp(World):
    def judged(self, name="judged", attempt="J"):
        out = self.output(self.follow, name, attempt)
        self.lines(self.follow, attempt, "first", out, "open", "close",
                   status="pass")
        return out

    def test_a_void_attempt_may_stand_beside_the_judged_one(self):
        void = self.output(self.follow, "void", "V")
        self.lines(self.follow, "V", "first", void, "open", "close",
                   status="inconclusive")
        out = self.judged()
        found = self.attempts(self.follow, {"J": out})
        self.assertEqual([(f["attempt"], f["judged"], f["void"])
                          for f in found],
                         [("V", False, True), ("J", True, False)])

    def test_a_second_attempt_that_is_not_void_is_refused(self):
        other = self.output(self.follow, "other", "N", protocol=True)
        self.lines(self.follow, "N", "first", other, "open", "close",
                   status="pass")
        out = self.judged()
        with self.assertRaisesRegex(
                ValueError, r"attempt N of table \w+ "
                r"\(status pass, output .*\) is not "
                r"void: the row of \w+-\d+ is not a protocol failure"):
            self.attempts(self.follow, {"J": out})

    def test_a_resumed_attempt_is_refused_and_a_plain_one_is_void(self):
        void = self.output(self.follow, "void", "V")
        self.lines(self.follow, "V", "first", void, "open", "close",
                   status="inconclusive")
        out = self.judged()
        self.assertTrue(self.attempts(self.follow, {"J": out})[0]["void"])
        resumed = self.output(self.follow, "resumed", "R")
        self.lines(self.follow, "R", "first", resumed, "open", "resume",
                   "close", status="inconclusive")
        with self.assertRaisesRegex(
                ValueError, r"attempt R of table \w+ "
                r"\(status inconclusive, output .*\) "
                r"is not void: it was resumed"):
            self.attempts(self.follow, {"J": out})

    def test_an_attempt_left_open_is_refused(self):
        left = self.output(self.follow, "left", "L")
        self.lines(self.follow, "L", "first", left, "open")
        out = self.judged()
        with self.assertRaisesRegex(ValueError, "was left open"):
            self.attempts(self.follow, {"J": out})

    def extension(self):
        """A judged second stage and its judged first stage."""
        first = self.output(self.follow, "first", "F")
        self.lines(self.follow, "F", "first", first, "open", "close",
                   status="pass")
        second = self.output(
            self.follow, "second", "S", grid="../first",
            schema=self.follow.t.schema("extension"))
        self.lines(self.follow, "S", "second", second, "open", "close",
                   status="pass")
        return first, second

    def test_the_judged_attempts_of_a_stage_and_of_its_first_stage(self):
        out = self.judged()
        self.assertEqual(d.judged_attempts(self.follow, out), {"J": out})
        first, second = self.extension()
        self.assertEqual(d.judged_attempts(self.follow, second),
                         {"S": second, "F": first})

    def test_a_judged_extension_and_its_first_stage_are_accepted(self):
        first, second = self.extension()
        found = d.table_attempts(self.follow, second, self.root, self.ledger)
        self.assertEqual([(f["attempt"], f["judged"], f["void"])
                          for f in found],
                         [("F", True, False), ("S", True, False)])
        # Naming the first stage alone leaves the second one unjudged.
        with self.assertRaisesRegex(ValueError, "attempt S .* is not void"):
            d.table_attempts(self.follow, first, self.root, self.ledger)

    def test_a_judged_attempt_must_be_in_the_output_named(self):
        out = self.judged()
        self.lines(self.follow, "J", "first", self.root / "elsewhere",
                   "resume")
        with self.assertRaisesRegex(ValueError, "ran in more than one"):
            d.table_attempts(self.follow, out, self.root, self.ledger)


class FirstStage(World):
    """The first stage's table `task31` obeys the rule of a follow-up's:
    at most one attempt that is not void, per table and stage."""

    def setUp(self):
        super().setUp()
        self.grid = timing.ENGINE

    def judged(self):
        out = self.output(self.grid, "judged", "J")
        self.lines(self.grid, "J", "first", out, "open", "close",
                   status="pass")
        return out

    def test_the_cells_of_the_table_are_the_sample(self):
        self.assertEqual(sorted(self.grid.t.names()), sorted(c.SAMPLE))

    def test_a_void_redraw_is_allowed(self):
        void = self.output(self.grid, "void", "V")
        self.lines(self.grid, "V", "first", void, "open", "close",
                   status="inconclusive")
        out = self.judged()
        found = d.table_attempts(self.grid, out, self.root, self.ledger)
        self.assertEqual([(f["attempt"], f["judged"], f["void"])
                          for f in found],
                         [("V", False, True), ("J", True, False)])

    def test_a_second_attempt_that_measured_is_refused(self):
        other = self.output(self.grid, "other", "N", protocol=True)
        self.lines(self.grid, "N", "first", other, "open", "close",
                   status="pass")
        out = self.judged()
        with self.assertRaisesRegex(
                ValueError, r"attempt N of table \w+ "
                r"\(status pass, output .*\) is not "
                r"void"):
            d.table_attempts(self.grid, out, self.root, self.ledger)

    def test_a_resumed_attempt_is_refused(self):
        resumed = self.output(self.grid, "resumed", "R")
        self.lines(self.grid, "R", "first", resumed, "open", "resume",
                   "close", status="inconclusive")
        out = self.judged()
        with self.assertRaisesRegex(ValueError, "it was resumed"):
            d.table_attempts(self.grid, out, self.root, self.ledger)

    def test_the_lines_of_another_table_of_the_ledger_are_not_read(self):
        # The follow-up's table shares the ledger: its attempts are no
        # attempt of the first stage's.
        other = self.output(self.follow, "f", "N", protocol=True)
        self.lines(self.follow, "N", "first", other, "open", "close",
                   status="pass")
        out = self.judged()
        found = d.table_attempts(self.grid, out, self.root, self.ledger)
        self.assertEqual([f["attempt"] for f in found], ["J"])


class Pins(unittest.TestCase):
    """The records of a timing grid that carry the pins, and the binding of
    those pins (and the identity grid's table) to the committed file."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="task31-pins-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name).resolve()
        self.now = a.seal(reviewed.FILE)

    def inventory(self, name, pins, resumed=(), **more):
        out = self.root / name
        out.mkdir()
        a.save(out / "inventory.json", dict(
            pins=pins, resumed=[dict(pins=p) for p in resumed], **more))
        return out

    def engine(self, entries, history=None):
        return tg.Grid(timing.table(dict(entries=entries,
                                         history=history or {})))

    def codes(self, engine, root):
        return [code["pins"] for code in d.pin_codes(engine, root)]

    def test_the_inventory_and_each_resumption_carry_pins(self):
        engine = self.engine([entry(SOURCE)])
        out = self.inventory("g", seal(OLD), [seal(OLD2), self.now])
        self.assertEqual(self.codes(engine, out),
                         [seal(OLD), seal(OLD2), self.now])

    def test_an_extension_carries_those_of_its_first_stage_too(self):
        engine = self.engine([entry(SOURCE)])
        self.inventory("first", seal("1" * 64), [seal("2" * 64)])
        second = self.inventory(
            "second", seal("3" * 64), [seal("4" * 64)], grid="../first",
            schema=engine.t.schema("extension"))
        self.assertEqual(self.codes(engine, second), [
            seal("3" * 64), seal("4" * 64), seal("1" * 64), seal("2" * 64)])

    def committed(self, entries):
        return dict(entries=entries, seal=self.now)

    def test_an_entry_that_is_no_source_of_the_grid_voids_no_grid(self):
        before = [entry(SOURCE)]
        after = before + [entry("tools/sequences/base-hol", kind="build"),
                          entry("src/1/ThmAttribute.sig", kind="heap")]
        engine = self.engine(after, {OLD: before})
        out = self.inventory("g", seal(OLD), [seal(OLD)])
        expected = d.pins_binding(engine, "timing grid", out,
                                  self.committed(after))
        self.assertEqual(expected, reviewed.pins(before, c.SOURCES))
        # The current file's seal is the committed pins by definition.
        out = self.inventory("h", self.now)
        d.pins_binding(engine, "timing grid", out, self.committed(after))

    def test_a_change_to_the_entry_of_a_measured_source_voids_the_grid(self):
        before = [entry(SOURCE)]
        after = [entry(SOURCE, blob="3" * 40)]
        engine = self.engine(after, {OLD: before})
        out = self.inventory("g", seal(OLD))
        with self.assertRaisesRegex(ValueError, "judged by pins that are "
                                    "not the committed table's"):
            d.pins_binding(engine, "timing grid", out, self.committed(after))

    def test_a_resumption_judged_by_other_pins_voids_the_grid(self):
        before, other = [entry(SOURCE)], [entry(SOURCE, blob="4" * 40)]
        engine = self.engine(before, {OLD: before, OLD2: other})
        out = self.inventory("g", seal(OLD), [seal(OLD2)])
        with self.assertRaisesRegex(ValueError, "not the committed"):
            d.pins_binding(engine, "timing grid", out,
                           self.committed(before))
        out = self.inventory("ok", seal(OLD), [seal(OLD)])
        d.pins_binding(engine, "timing grid", out, self.committed(before))

    def test_the_first_stage_of_an_extension_voids_it_too(self):
        before, other = [entry(SOURCE)], [entry(SOURCE, blob="4" * 40)]
        engine = self.engine(before, {OLD: before, OLD2: other})
        self.inventory("first", seal(OLD2))
        second = self.inventory("second", seal(OLD), grid="../first",
                                schema=engine.t.schema("extension"))
        with self.assertRaisesRegex(ValueError, "not the committed"):
            d.pins_binding(engine, "timing grid", second,
                           self.committed(before))
        self.inventory("first2", seal(OLD))
        second = self.inventory("second2", seal(OLD), grid="../first2",
                                schema=engine.t.schema("extension"))
        d.pins_binding(engine, "timing grid", second, self.committed(before))

    def test_an_unknown_seal_of_the_pins_is_refused(self):
        engine = self.engine([entry(SOURCE)])
        out = self.inventory("g", seal("c" * 64))
        with self.assertRaisesRegex(ValueError, "changed pins"):
            d.pins_binding(engine, "timing grid", out,
                           self.committed([entry(SOURCE)]))

    def test_the_identity_grid_must_hold_the_committed_file(self):
        document = self.committed([entry(SOURCE)])
        held = d.identity_binding(
            dict(attributed=dict(file=self.now)), document)
        self.assertEqual(held, self.now)
        # An earlier version of the file is a grid to run again, even where
        # the timing grids replay by its history.
        with self.assertRaisesRegex(ValueError, "run it again"):
            d.identity_binding(dict(attributed=dict(file=seal(OLD))),
                               document)
        with self.assertRaisesRegex(ValueError, "records no reviewed"):
            d.identity_binding(dict(attributed=dict(file=None)), document)


class Modules(unittest.TestCase):
    """Every local module that a decision imports, to the transitive closure
    (function-level imports included; this directory, allocator-counter/ and
    ../compatibility/), is sealed for that side or reached only by an
    exempt import edge with a stated reason. "Sealed" is: in a seal list
    that a record of the side carries (and its replay checks), or, for the
    modules of timing_grid.REPLAY_CODE that the first-stage record does not
    carry (timing_grid.py and acceptance.py are carried as `engine` and
    `acceptance`), a module whose result the replay recomputes and compares
    with the record (each cell's archived report, "changed point
    analysis"; decisions.json, "changed TASK31 decisions"): a change of
    one can make a replay refuse but cannot alter a recorded decision. Only
    a follow-up's counts carry their seals (`replaces.code`). Code run by
    path (run_paired) is not seen as an import: it is a root."""

    # The reasons of the exempt edges.
    TOOLCHAIN = (
        "private_runtime builds and checks the runtime (loading, "
        "prepare_patch, check_patch, path_schema); TASK31 code uses only its "
        "harness_identity, tree_outside_performance, AGENT_STATE and "
        "PERFORMANCE_DIR, which use none of them (measurement calls "
        "harness_identity too, through clean_head)")
    CONTRACTS = (
        "run_paired.main imports it under --prior-contracts, "
        "--staging-contracts or --public-contracts, which no TASK31 command "
        "passes (the paired runner is run for --performance-pairs); "
        "run_paired.py itself is sealed")
    TASK30_TABLE = (
        "task30_grid builds TASK30's own table (its cases and pins) when "
        "imported; the disposition's replay reads neither, and task30_grid "
        "itself is sealed by task31_dispose.CODE")
    TASK30_IDENTITY = (
        "task31_grid takes the constants PAIRED, INSTALLED and SEALED[1:5] "
        "from task30_grid for the timing table and calls no function of "
        "it; no identity code reads those constants or task30_grid, and no "
        "identity seal covers task30_grid.py")
    TASK30_CONSTANTS = (
        "task31_grid takes the constants PAIRED, INSTALLED and SEALED[1:5] "
        "from task30_grid and no function. No seal list of a timing grid "
        "has task30_grid.py: what binds the constants is the table's "
        "SEALED, whose names the check compares as a set with the record's "
        "and whose files it compares by seal, so a changed INSTALLED or "
        "SEALED[1:5] refuses a recorded grid (PAIRED only through the "
        "names of INSTALLED)")
    ALLOCATION_BUILD = (
        "the allocation matrix's toolchain building (loading, "
        "prepare_patch, bootstrap_probe), which the disposition's replay of "
        "an allocation grid does not do")
    ALLOCATION_CASES = (
        "allocation_matrix builds the TASK30 task from it, which a TASK31 "
        "allocation grid does not replay: it replays as task `task31`, "
        "whose cases come from the sealed task31_cases (a change that "
        "breaks the TASK30 task fails the import, a refusal); the "
        "harness_files binding of the blob is a record of the "
        "measurement, which the replay does not compare")

    ALLOCATION_TASK37 = (
        "allocation_matrix imports the TASK37 case lists only when a "
        "TASK37 task is asked for, which a TASK31 allocation grid never "
        "does")

    @staticmethod
    def edges(reason, *edges):
        return {edge: reason for edge in edges}

    @classmethod
    def runtime_edges(cls, *modules):
        found = cls.edges(cls.CONTRACTS, *(
            ("run_paired", m, "main") for m in (
                "prior_contracts", "staging_contracts", "public_contracts")))
        found.update(cls.edges(cls.TOOLCHAIN, *(
            ("private_runtime", m, None) for m in modules)))
        return found

    @classmethod
    def exempt(cls, side):
        if side == "identity":
            found = cls.runtime_edges(
                "loading", "path_schema", "prepare_patch", "check_patch")
            found.update(cls.edges(
                cls.TASK30_IDENTITY, ("task31_grid", "task30_grid", None)))
        elif side == "timing":
            found = cls.runtime_edges(
                "loading", "path_schema", "prepare_patch", "check_patch")
            found.update(cls.edges(
                cls.TASK30_CONSTANTS, ("task31_grid", "task30_grid", None)))
        else:
            found = cls.runtime_edges(
                "loading", "prepare_patch", "check_patch")
            found.update(cls.edges(
                cls.TASK30_TABLE, ("task30_grid", "task30_cases", None),
                ("task30_grid", "task30_pins", None)))
            found.update(cls.edges(
                cls.ALLOCATION_BUILD,
                ("allocation_matrix", "loading", None),
                ("allocation_matrix", "prepare_patch", None),
                ("allocation_matrix", "bootstrap_probe", "toolchain")))
            found.update(cls.edges(
                cls.ALLOCATION_CASES,
                ("allocation_matrix", "task30_cases", None)))
            found.update(cls.edges(
                cls.ALLOCATION_TASK37,
                ("allocation_matrix", "task37_cases", "task37_matrix"),
                ("allocation_matrix", "task37_cases", "task37_client")))
        return found

    @staticmethod
    def stems(names):
        return {Path(n).stem for n in names}

    def covered(self, side, roots, sealed, sources=None):
        sources = sources or ic.sources()
        exempt = self.exempt(side)
        sealed = self.stems(sealed)
        found, used = ic.closure(sources, roots, exempt)
        self.assertEqual(
            sorted(found - sealed), [],
            "%s: imported (transitively) and neither sealed nor reached "
            "only by an exempt edge" % side)
        # Every exempt edge is made by a module of the closure, and what it
        # leaves out is not sealed (else it needs no exemption).
        self.assertEqual(sorted(set(exempt) - used, key=str), [])
        self.assertEqual(
            sorted(e for e in exempt if e[1] in sealed), [])
        return found

    # run_paired is a root of the identity and the timing process: it is
    # executed by path (runpy in task31_snapshot, a subprocess of
    # acceptance), which an import graph does not see.
    IDENTITY_ROOTS = ("task31_identity_grid", "task31_identity",
                      "task31_attribution", "task31_snapshot",
                      "run_paired")
    TIMING_ROOTS = ("task31_grid", "task31_followup", "run_paired")

    def identity(self, sources=None):
        import task31_identity_grid as idgrid
        return self.covered("identity", self.IDENTITY_ROOTS,
                            idgrid.IDENTITY_CODE, sources)

    def timing_sealed(self):
        return (*timing.SEALED, "task31_grid.py", "task31_followup.py",
                *tg.REPLAY_CODE)

    def test_the_identity_modules_import_only_sealed_code(self):
        import task31_identity_grid as idgrid
        found = self.identity()
        self.assertIn("private_runtime", found)
        self.assertIn("private_runtime", self.stems(idgrid.IDENTITY_CODE))
        self.assertIn("allocator-counter/private_runtime.py",
                      idgrid.IDENTITY_CODE)
        self.assertIn("task31_pins.py", idgrid.IDENTITY_CODE)

    def test_the_timing_modules_import_only_sealed_code(self):
        found = self.covered("timing", self.TIMING_ROOTS,
                             self.timing_sealed())
        self.assertIn("private_runtime", found)

    def test_the_disposition_imports_only_sealed_code(self):
        import task31_identity_grid as idgrid
        # The disposition replays the identity grid (IDENTITY_CODE), the
        # timing grid (the timing seals) and the allocation grid.
        sealed = (*d.CODE, *idgrid.IDENTITY_CODE, *timing.SEALED,
                  *tg.REPLAY_CODE)
        self.covered("disposition", ("task31_dispose",), sealed)
        # The harness the disposition compares the allocation grid with.
        self.assertIn("task30_grid.py", d.CODE)
        self.assertIn("task31_pins.py", d.CODE)
        self.assertIs(d.base30, __import__("task30_grid"))

    def test_every_exempt_edge_is_made_only_where_it_is_said_to_be(self):
        sources = ic.sources()
        for side in ("identity", "timing", "disposition"):
            for edge in self.exempt(side):
                with self.subTest(side=side, edge=edge):
                    self.assertIn(edge, ic.edges(sources, edge[0]))

    def test_a_new_import_of_identity_code_is_found(self):
        sources = ic.sources()
        self.identity(sources)
        for label, name, line in (
                ("private_runtime", "private_runtime",
                 "import control_schema"),
                ("allocation_matrix, directly", "task31_identity",
                 "import allocation_matrix"),
                ("loading, directly", "task31_identity", "import loading"),
                ("task30_grid, directly", "task31_identity",
                 "import task30_grid"),
                ("a contracts module, by the timing import",
                 "timing_grid", "import prior_contracts")):
            with self.subTest(label):
                changed = dict(sources)
                changed[name] += "\n" + line + "\n"
                with self.assertRaises(AssertionError):
                    self.identity(changed)

    def test_a_dropped_identity_seal_is_found(self):
        import task31_identity_grid as idgrid
        sources = ic.sources()
        for name in ("allocator-counter/private_runtime.py",
                     "task31_pins.py"):
            with self.subTest(name), self.assertRaises(AssertionError):
                self.covered(
                    "identity", self.IDENTITY_ROOTS,
                    [n for n in idgrid.IDENTITY_CODE if n != name], sources)

    def test_run_paired_is_sealed_though_no_import_reaches_it(self):
        # Hide the one import of run_paired (runtime_metrics.smoke), and
        # drop its seal: the root alone makes the closure demand the seal.
        import task31_identity_grid as idgrid
        sources = dict(ic.sources())
        self.assertIn("import run_paired as rp", sources["runtime_metrics"])
        sources["runtime_metrics"] = sources["runtime_metrics"].replace(
            "import run_paired as rp", "rp = __import__('run_paired')")
        self.assertNotIn(("runtime_metrics", "run_paired", "smoke"),
                         ic.edges(sources, "runtime_metrics"))
        pattern = "neither sealed nor reached only by an exempt edge"
        unsealed = [n for n in idgrid.IDENTITY_CODE if "run_paired" not in n]
        with self.assertRaisesRegex(AssertionError, pattern):
            self.covered("identity", self.IDENTITY_ROOTS, unsealed, sources)
        timing_unsealed = [n for n in self.timing_sealed()
                           if "run_paired" not in n]
        with self.assertRaisesRegex(AssertionError, pattern):
            self.covered("timing", self.TIMING_ROOTS, timing_unsealed,
                         sources)
        # Sealed, it checks.
        self.covered("identity", self.IDENTITY_ROOTS,
                     idgrid.IDENTITY_CODE, sources)
        self.covered("timing", self.TIMING_ROOTS, self.timing_sealed(),
                     sources)


if __name__ == "__main__":
    unittest.main()
