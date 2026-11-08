#!/usr/bin/env python3
"""The attempts and the pins the TASK31 disposition binds (task31_dispose.py),
against real engines and real ledgers (task31_followup.table, tg.Ledger, the
void rule of void_attempts.py), with nothing under test replaced."""
import argparse
from pathlib import Path
import tempfile
import unittest

import acceptance as a
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
                ValueError, r"attempt N \(status pass, output .*\) is not "
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
                ValueError, r"attempt R \(status inconclusive, output .*\) "
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
                ValueError, r"attempt N \(status pass, output .*\) is not "
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
    def test_every_module_the_decision_imports_is_sealed(self):
        import ast
        import task31_identity_grid as idgrid
        sealed = set(d.CODE) | set(idgrid.IDENTITY_CODE)
        for name in ("task31_dispose.py", "task31_grid.py",
                     "task31_followup.py"):
            tree = ast.parse((a.HERE / name).read_text())
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    modules = [n.name for n in node.names]
                elif isinstance(node, ast.ImportFrom):
                    modules = [node.module]
                else:
                    continue
                for module in modules:
                    if (a.HERE / (module + ".py")).is_file():
                        self.assertIn(module + ".py", sealed,
                                      "%s imports %s" % (name, module))
        # The harness the disposition compares the allocation grid with.
        self.assertIn("task30_grid.py", d.CODE)
        self.assertIn("task31_pins.py", d.CODE)
        self.assertIs(d.base30, __import__("task30_grid"))


if __name__ == "__main__":
    unittest.main()
