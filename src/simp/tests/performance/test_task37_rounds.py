#!/usr/bin/env python3
"""The TASK37 follow-up rounds (task37_rounds.py, decision 47): the
declarations, the tables, the pairs rule, the declaration order, the command
line and the chaining of the rounds in the disposition; and that round 1
(task37_followup.py) is unchanged."""
import contextlib
import io
import json
import subprocess
import tempfile
import types
import unittest
from pathlib import Path
from unittest import mock

import acceptance as a
import task31_dispose as d31
import task37_dispose as d
import task37_followup as f
import task37_grid as g
import task37_rounds as r
import timing_grid as tg

KEY = "matrix-4"
CELLS = g.PARTS[KEY][:3]


DECISION = "user decision of round 2 (recorded)"


def declare_in(root, key, number, cells, pairs=80, **more):
    path = Path(root) / ("task37_%s_%s_followup%d_cells.json" % (
        key.split("-")[0], key.split("-")[1], number))
    doc = dict(schema=r.SCHEMA, shard=key, round=number, cells=list(cells),
               pairs=pairs, decision=DECISION)
    doc.update(more)
    path.write_text(json.dumps(doc))
    return path


class RoundOneUnchanged(unittest.TestCase):
    def test_the_driver_of_round_one_is_byte_identical(self):
        # git hash-object of task37_followup.py before decision 47: the
        # recorded follow-ups' driver seal depends on these bytes
        data = Path(f.__file__).read_bytes()
        blob = subprocess.run(
            ["git", "hash-object", "--stdin"], input=data, check=True,
            stdout=subprocess.PIPE).stdout.decode().strip()
        self.assertEqual(blob, "5c074d32c36d3e5576e1387f8b463ae1b583e0c8")

    def test_the_observables_of_round_one(self):
        for key in g.SHARD_KEYS:
            kind, n = key.split("-")
            t = f.table(key, g.PARTS[key][:1], g.GRIDS["task37-" + key])
            self.assertEqual(t.name, "task37-%s-followup" % key)
            self.assertEqual(t.label, "TASK37-%s-FOLLOWUP" % key.upper())
            self.assertEqual(
                f.declaration_file(key).name,
                "task37_%s_%s_followup_cells.json" % (kind, n))
            self.assertEqual(
                t.counts.name,
                "task37_%s_%s_followup_iterations.json" % (kind, n))
            self.assertEqual(t.seed, "task37-%s-followup-layout-1" % key)
            self.assertEqual(t.pairs, 2 * g.PAIRS)
            self.assertEqual(t.sealed, f.SEALED[key] + (
                f.declaration_file(key).name,))
            self.assertEqual(t.drivers, g.DRIVERS)


class Keys(unittest.TestCase):
    def test_a_key_is_a_shard_or_a_shard_and_a_round(self):
        self.assertEqual(r.parse_key("matrix-4"), ("matrix-4", 1))
        self.assertEqual(r.parse_key("matrix-4.2"), ("matrix-4", 2))
        self.assertEqual(r.parse_key("client-1.9"), ("client-1", 9))
        self.assertEqual(r.key_text("matrix-4", 1), "matrix-4")
        self.assertEqual(r.key_text("matrix-4", 3), "matrix-4.3")
        for bad in ("matrix-4.1", "matrix-4.0", "matrix-4.10", "matrix-4.x",
                    "matrix-4.", "matrix-9.2", ".2", "", "matrix-4.02"):
            with self.assertRaises(ValueError, msg=bad):
                r.parse_key(bad)

    def test_the_names_of_a_round(self):
        self.assertEqual(r.name_of(KEY, 2), "task37-matrix-4-followup2")
        self.assertEqual(r.file_of(KEY, 3).name,
                         "task37_matrix_4_followup3_iterations.json")
        self.assertEqual(r.declaration_file(KEY, 2).name,
                         "task37_matrix_4_followup2_cells.json")
        self.assertEqual(r.declaration_name(KEY, 1),
                         "task37_matrix_4_followup_cells.json")
        self.assertEqual(r.declaration_name(KEY, 2),
                         "task37_matrix_4_followup2_cells.json")
        with self.assertRaises(ValueError):
            r.declaration_file(KEY, 1)


class Declarations(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        patch = mock.patch.object(
            r, "declaration_file", lambda key, n: self.root / (
                "task37_%s_%s_followup%d_cells.json" % (
                    key.split("-")[0], key.split("-")[1], n)))
        patch.start()
        self.addCleanup(patch.stop)

    def load(self, number=2, **more):
        path = declare_in(self.root, KEY, number, more.pop(
            "cells", CELLS[:2]), **more)
        return r.load_declaration(KEY, number, path, previous=CELLS)

    def test_a_declaration_gives_the_cells_and_the_pairs(self):
        self.assertEqual(self.load(pairs=100), dict(
            cells=tuple(CELLS[:2]), pairs=100, decision=DECISION))

    def test_a_decision_is_a_non_empty_reference(self):
        for bad in ("", "  ", None, 7, ["x"], r.PLACEHOLDER):
            with self.assertRaisesRegex(ValueError, "no decision",
                                        msg=bad):
                self.load(decision=bad)
        path = self.root / "nodecision.json"
        path.write_text(json.dumps(dict(
            schema=r.SCHEMA, shard=KEY, round=2, cells=CELLS[:1],
            pairs=80)))
        with self.assertRaisesRegex(ValueError, "is not a"):
            r.load_declaration(KEY, 2, path, previous=CELLS)

    def test_cells_are_a_subset_of_the_round_before(self):
        with self.assertRaisesRegex(ValueError, "subset"):
            self.load(cells=[g.PARTS[KEY][-1]])
        with self.assertRaisesRegex(ValueError, "subset"):
            self.load(cells=[])
        with self.assertRaisesRegex(ValueError, "subset"):
            self.load(cells=[CELLS[0], CELLS[0]])

    def test_the_round_and_shard_are_those_of_the_file_name(self):
        with self.assertRaisesRegex(ValueError, "not round 2"):
            self.load(round=3)
        with self.assertRaisesRegex(ValueError, "not round 2"):
            self.load(shard="matrix-3")
        with self.assertRaisesRegex(ValueError, "not round 2"):
            self.load(round="2")

    def test_the_schema_and_the_fields_are_exact(self):
        with self.assertRaisesRegex(ValueError, "is not a"):
            self.load(schema="other")
        with self.assertRaisesRegex(ValueError, "is not a"):
            self.load(extra=1)
        path = self.root / "p.json"
        path.write_text(json.dumps(dict(schema=r.SCHEMA, shard=KEY,
                                        round=2, cells=CELLS[:1])))
        with self.assertRaisesRegex(ValueError, "is not a"):
            r.load_declaration(KEY, 2, path, previous=CELLS)

    def test_the_pairs_are_a_positive_integer(self):
        for bad in (0, -10, 1.5, "80", True, None):
            with self.assertRaisesRegex(ValueError, "positive", msg=bad):
                self.load(pairs=bad)

    def test_a_gap_is_refused(self):
        # round 3 with no round 2 file
        path = declare_in(self.root, KEY, 3, CELLS[:1])
        with self.assertRaisesRegex(ValueError, "a gap"):
            r.load_declaration(KEY, 3, path)
        # round 2 with no round 1 declaration
        with mock.patch.object(f, "declaration_file",
                               lambda key: self.root / "none.json"):
            with self.assertRaisesRegex(ValueError, "round 1\\) declared"):
                r.load_declaration(KEY, 2, declare_in(
                    self.root, KEY, 2, CELLS[:1]))

    def test_round_three_is_a_subset_of_round_twos_cells(self):
        declare_in(self.root, KEY, 2, CELLS[:2])
        with mock.patch.object(f, "declaration_file",
                               lambda key: self.root / "r1.json"), \
                mock.patch.object(f, "load_declaration",
                                  lambda key: tuple(CELLS)):
            (self.root / "r1.json").write_text("{}")
            three = declare_in(self.root, KEY, 3, CELLS[:1])
            self.assertEqual(
                r.load_declaration(KEY, 3, three)["cells"], (CELLS[0],))
            bad = declare_in(self.root, KEY, 3, [CELLS[2]])
            with self.assertRaisesRegex(ValueError, "subset"):
                r.load_declaration(KEY, 3, bad)

    def test_declared_discovers_the_files_that_exist_and_refuses_a_gap(
            self):
        self.assertEqual(r.declared(), {})
        declare_in(self.root, KEY, 3, CELLS[:1])
        with self.assertRaises(ValueError):
            r.declared()


class Tables(unittest.TestCase):
    def test_a_round_is_a_targeted_table(self):
        shard = g.TABLES["task37-" + KEY]
        for number in (2, 3):
            t = r.table(KEY, number, CELLS[:2], 80, revisions=())
            self.assertIsNone(t.replaces)
            self.assertEqual(t.name, "task37-matrix-4-followup%d" % number)
            self.assertEqual(t.label, "TASK37-MATRIX-4-FOLLOWUP%d" % number)
            self.assertEqual(
                t.counts.name,
                "task37_matrix_4_followup%d_iterations.json" % number)
            self.assertEqual(t.counts, r.file_of(KEY, number))
            self.assertEqual(t.seed, "%s-layout-1" % t.name)
            self.assertEqual(t.pairs, 80)
            self.assertEqual(set(t.names()), set(CELLS[:2]))
            self.assertEqual(t.family, shard.family)
            self.assertEqual((t.sources, t.pinned, t.pin_file),
                             (shard.sources, shard.pinned, shard.pin_file))
            self.assertEqual(
                (t.samples, t.schedule, t.baseline, t.headroom,
                 t.seconds, t.target, t.max_pairs, t.fixed_seconds),
                (shard.samples, shard.schedule, shard.baseline,
                 shard.headroom, shard.seconds, shard.target,
                 shard.max_pairs, True))
            self.assertEqual(t.driver, Path(r.__file__))
            want = f.SEALED[KEY] + ("task37_followup.py",) + tuple(
                r.declaration_name(KEY, i) for i in range(1, number + 1))
            self.assertEqual(t.sealed, want)
            self.assertEqual(t.drivers, g.DRIVERS)
            self.assertEqual(t.engines, g.ENGINES)
        self.assertNotIn("task37_matrix_4_followup3_cells.json",
                         r.table(KEY, 2, CELLS[:1], 80).sealed)

    def test_the_seeds_and_counts_do_not_clash_with_other_tables(self):
        t = r.table(KEY, 2, CELLS[:1], 80)
        others = [x for x in g.TABLES.values()]
        self.assertNotIn(t.seed, [x.seed for x in others])
        self.assertNotIn(t.counts, [x.counts for x in others])
        self.assertNotIn(t.name, g.GRIDS)
        self.assertNotEqual(
            t.seed, f.table(KEY, CELLS[:1], g.GRIDS["task37-" + KEY]).seed)

    def test_bad_arguments_are_refused(self):
        for number, cells, pairs in (
                (1, CELLS[:1], 80), (2, (), 80),
                (2, (g.PARTS["matrix-1"][0],), 80), (2, CELLS[:1], 0),
                (2, CELLS[:1], 10 ** 6), (2, CELLS[:1], 8.0)):
            with self.assertRaises(ValueError, msg=(number, cells, pairs)):
                r.table(KEY, number, cells, pairs)

    def test_the_engine_is_declared_by_table_name(self):
        declaration = dict(cells=tuple(CELLS[:1]), pairs=80,
                           decision=DECISION)
        built, engine = r.declare(KEY, 2, declaration)
        self.assertIsInstance(engine, r.Rounds)
        self.assertEqual((engine.key, engine.number), (KEY, 2))
        grids, declared = dict(r.GRIDS), dict(r.DECLARED)
        with mock.patch.dict(r.GRIDS, {built.name: engine}, clear=True), \
                mock.patch.dict(r.DECLARED, {KEY: {2: declaration}},
                                clear=True):
            self.assertEqual(r.commands(), {"matrix-4.2": engine})
            with mock.patch.object(engine, "main", return_value=7) as run:
                self.assertEqual(r.main(["matrix-4.2", "pilot", "--x"]), 7)
            run.assert_called_once_with(["pilot", "--x"])
            self.assertIs(r.engine_before(KEY, 3), engine)
        self.assertEqual(r.GRIDS, grids)
        self.assertEqual(r.DECLARED, declared)

    def test_the_module_holds_the_engines_of_the_declaration_files(self):
        self.assertEqual(r.DECLARED, r.declared())
        names = {r.name_of(k, n) for k, rounds in r.DECLARED.items()
                 for n in rounds}
        self.assertEqual(set(r.GRIDS), names)
        self.assertEqual(set(r.TABLES), names)
        for key, rounds in r.DECLARED.items():
            for number, declaration in rounds.items():
                name = r.name_of(key, number)
                self.assertEqual(set(r.TABLES[name].names()),
                                 set(declaration["cells"]))
                self.assertEqual(r.TABLES[name].pairs,
                                 declaration["pairs"])
                self.assertTrue(declaration["decision"].strip())
        self.assertEqual(set(r.commands()), {
            r.key_text(k, n) for k, rounds in r.DECLARED.items()
            for n in rounds})

    def test_the_replay_code_has_no_replaces_option(self):
        built, engine = r.declare(KEY, 2, dict(
            cells=tuple(CELLS[:1]), pairs=80, decision=DECISION))
        self.assertIsNone(built.replaces)


class Cli(unittest.TestCase):
    def test_every_command_is_refused_where_none_is_declared(self):
        for argv in ([], ["matrix-4.2", "run"], ["matrix-4", "run"],
                     ["matrix-4.1", "run"], ["nonsense"]):
            err = io.StringIO()
            with mock.patch.dict(r.GRIDS, {}, clear=True), \
                    mock.patch.dict(r.DECLARED, {}, clear=True), \
                    contextlib.redirect_stderr(err):
                self.assertEqual(r.main(argv), tg.REFUSED, argv)
            self.assertIn("no such TASK37 follow-up round", err.getvalue())

    def test_derive_pairs_needs_the_round_before_not_this_round(self):
        with mock.patch.object(r, "derive_main", return_value=3) as run:
            self.assertEqual(r.main(["matrix-4.2", "derive-pairs",
                                     "--grid", "x"]), 3)
        run.assert_called_once_with(KEY, 2, ["--grid", "x"])
        # round 1's key has no derive-pairs
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            self.assertEqual(r.main(["matrix-4", "derive-pairs"]),
                             tg.REFUSED)


def report(width, success=True):
    """A report whose control's gated intervals have half log-width
    `width`."""
    import math
    ci = [math.exp(-width), math.exp(width)]
    metrics = {m: dict(paired_ratio_bootstrap_95_percent=ci)
               for m in a.EQUIVALENCE_POLICY["gated_timing"]}
    return dict(success=success, workloads=[dict(control=dict(
        metrics=metrics))])


class FakeEngine:
    def __init__(self, limits=(0.015, 120), name="task37-matrix-4-followup"):
        self.t = types.SimpleNamespace(target=limits[0],
                                       max_pairs=limits[1], name=name)
        self.limits = limits

    def limits_of(self, inventory):
        return self.limits

    def cell_pairs(self, counts, key, default):
        return counts.get("pairs_by_cell", {}).get("%s-%d" % key, default)


class PairsRule(unittest.TestCase):
    def found(self, widths, second=None, plan=None, per_cell=None):
        stage1 = {("c", s): report(w) for s, w in widths.items()}
        first = dict(pairs=40, iterations=dict(pairs_by_cell=per_cell or {}))
        inventory = dict(plan=[["c", s, p] for s, p in (plan or {}).items()])
        return dict(inventory=inventory, first=first, stage1=stage1,
                    stage2={("c", s): report(w)
                            for s, w in (second or {}).items()})

    def test_a_narrow_control_gives_twice_the_pairs(self):
        found = self.found({1: 0.01})
        per = r.decisive_pairs(FakeEngine(), found, ["c-1"])
        self.assertEqual(per, {"c-1": 80})

    def test_a_wide_control_scales_to_tens_and_the_cap(self):
        engine = FakeEngine()
        wide = 0.015 * (95 / 40) ** 0.5     # wanted 95 pairs
        per = r.decisive_pairs(engine, self.found({1: wide, 2: 0.5}),
                               ["c-1", "c-2"])
        self.assertEqual(per, {"c-1": 100, "c-2": 120})
        self.assertEqual(per["c-1"], tg.second_stage_pairs(
            wide, 40, 0.015, 120))

    def test_the_pairs_of_the_report_come_from_the_cells_counts(self):
        found = self.found({1: 0.02}, per_cell={"c-1": 30})
        want = tg.second_stage_pairs(0.02, 30, 0.015, 120)
        self.assertEqual(r.decisive_pairs(FakeEngine(), found, ["c-1"]),
                         {"c-1": want})

    def test_the_second_stage_is_decisive_where_a_cell_has_one(self):
        found = self.found({1: 0.5, 2: 0.5}, second={1: 0.01},
                           plan={1: 90})
        per = r.decisive_pairs(FakeEngine(), found, ["c-1", "c-2"])
        # c-1: the second stage's control and its 90 pairs; c-2: the first
        self.assertEqual(per["c-1"], tg.second_stage_pairs(
            0.01, 90, 0.015, 120))
        self.assertEqual(per["c-1"], 120)   # twice 90, capped
        self.assertEqual(per["c-2"], 120)

    def test_the_declared_pairs_are_the_largest_of_the_cells(self):
        wide = 0.015 * (95 / 40) ** 0.5
        found = self.found({1: 0.01, 2: wide})
        self.assertEqual(r.declared_pairs(FakeEngine(), found,
                                          ["c-1", "c-2"]),
                         (100, {"c-1": 80, "c-2": 100}))
        r.check_pairs(FakeEngine(), found, ["c-1", "c-2"], 100)
        for bad in (80, 90, 110, 120):
            with self.assertRaisesRegex(ValueError, "the rule gives 100"):
                r.check_pairs(FakeEngine(), found, ["c-1", "c-2"], bad)

    def test_a_missing_or_unmeasured_cell_is_refused(self):
        with self.assertRaisesRegex(ValueError, "no report"):
            r.decisive_pairs(FakeEngine(), self.found({1: 0.01}), ["c-2"])
        found = self.found({1: 0.01})
        found["stage1"][("c", 1)] = report(0.01, success=False)
        with self.assertRaisesRegex(ValueError, "did not measure"):
            r.decisive_pairs(FakeEngine(), found, ["c-1"])

    def test_the_limits_of_the_counts_rule_the_cap(self):
        engine = FakeEngine(limits=(0.02, 200))
        found = self.found({1: 0.5})
        self.assertEqual(r.decisive_pairs(engine, found, ["c-1"]),
                         {"c-1": 200})

    def test_nothing_of_a_candidate_is_read(self):
        found = self.found({1: 0.01})
        found["stage1"][("c", 1)]["workloads"][0]["candidate"] = "x"
        self.assertEqual(r.decisive_pairs(FakeEngine(), found, ["c-1"]),
                         {"c-1": 80})


class DerivePairs(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.rows = [dict(case="c", size=1, protocol=True),
                     dict(case="c", size=10, protocol=True)]
        (self.root / "decisions.json").write_text(json.dumps(
            dict(workloads=self.rows)))
        self.classes = {1: "inconclusive", 10: "pass"}
        for target, value in (
                (r, ("engine_before", lambda key, n: FakeEngine())),
                (r, ("stage_reports", lambda engine, grid: dict(
                    inventory={}, first=dict(pairs=40, iterations={}),
                    stage1={("c", 1): report(0.01),
                            ("c", 10): report(0.01)}, stage2={}))),
                (tg, ("classify_row",
                      lambda w: self.classes[w["size"]]))):
            patch = mock.patch.object(target, *value)
            patch.start()
            self.addCleanup(patch.stop)

    def test_the_open_cells_and_their_pairs_are_derived(self):
        declaration, per = r.derive_pairs(KEY, 2, self.root)
        self.assertEqual(declaration, dict(
            schema=r.SCHEMA, shard=KEY, round=2, cells=["c-1"], pairs=80,
            decision=r.PLACEHOLDER))
        self.assertEqual(per, {"c-1": 80})

    def test_the_cells_are_every_open_cell_and_there_is_no_choice(self):
        self.classes[10] = "inconclusive"
        declaration, per = r.derive_pairs(KEY, 2, self.root)
        self.assertEqual(declaration["cells"], ["c-1", "c-10"])
        with self.assertRaises(TypeError):
            r.derive_pairs(KEY, 2, self.root, ["c-1"])
        self.classes[1] = self.classes[10] = "pass"
        with self.assertRaisesRegex(ValueError, "exactly .*none"):
            r.derive_pairs(KEY, 2, self.root)

    def test_the_command_prints_the_declaration(self):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(r.main(["matrix-4.2", "derive-pairs", "--grid",
                                     str(self.root)]), 0)
        last = json.loads(out.getvalue().splitlines()[-1])
        self.assertEqual(last["pairs"], 80)
        self.assertEqual(last["cells"], ["c-1"])
        self.assertEqual(last["decision"], r.PLACEHOLDER)
        self.assertIn("c-1: 80 pairs", out.getvalue())
        with contextlib.redirect_stderr(io.StringIO()), \
                self.assertRaises(SystemExit):
            r.main(["matrix-4.2", "derive-pairs", "--grid", str(self.root),
                    "--cells", "c-1"])

    def test_the_cells_of_a_round_are_exactly_the_open_ones(self):
        r.check_cells(["c-1", "c-10"], ["c-10", "c-1"], 2)
        for names in (["c-1"], ["c-1", "c-10", "c-2"], ["c-2"], []):
            with self.assertRaisesRegex(ValueError, "exactly"):
                r.check_cells(["c-1", "c-10"], names, 2)
        with self.assertRaisesRegex(ValueError, "exactly"):
            r.check_cells([], [], 2)


class Ordering(unittest.TestCase):
    """The declaration of round 2 follows round 1's counts and precedes
    round 2's (a real repository)."""

    def git(self, *args):
        return subprocess.run(
            ["git", "-C", str(self.repo), "-c", "user.name=t", "-c",
             "user.email=t@t", *args], check=True, text=True,
            stdout=subprocess.PIPE).stdout.strip()

    def commit(self, **files):
        for name, text in files.items():
            (self.repo / name).write_text(text)
        self.git("add", "-A")
        self.git("commit", "-qm", "c")
        return self.git("rev-parse", "HEAD")

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name).resolve()
        self.git("init", "-q", ".")
        self.before = ["c1.json"]
        for target, name, value in (
                (r, "declaration_file", lambda key, n: self.repo / "d.json"),
                (r, "previous_counts_files", lambda key, n: [
                    self.repo / x for x in self.before])):
            patch = mock.patch.object(target, name, value)
            patch.start()
            self.addCleanup(patch.stop)

    def order(self, candidate, counts):
        r.check_declaration_order(self.repo, candidate, KEY, 2, counts)

    def test_declared_after_round_ones_counts_before_round_twos(self):
        self.commit(**{"c1.json": "1"})
        self.commit(**{"d.json": "{}"})
        counts = self.commit(**{"c2.json": "2"})
        later = self.commit(**{"o.txt": "x"})
        self.order(later, counts)

    def test_a_declaration_before_round_ones_counts_is_refused(self):
        self.commit(**{"d.json": "{}"})
        counts = self.commit(**{"c1.json": "1"})
        with self.assertRaisesRegex(ValueError, "not a descendant"):
            self.order(counts, counts)

    def test_a_declaration_after_round_twos_counts_is_refused(self):
        self.commit(**{"c1.json": "1"})
        counts = self.commit(**{"c2.json": "2"})
        late = self.commit(**{"d.json": "{}"})
        with self.assertRaisesRegex(ValueError, "not an ancestor"):
            self.order(late, counts)

    def test_a_declaration_in_the_counts_commit_is_refused(self):
        self.commit(**{"c1.json": "1"})
        both = self.commit(**{"d.json": "{}", "c2.json": "2"})
        with self.assertRaisesRegex(ValueError, "change only that file"):
            self.order(both, both)

    def test_a_declaration_with_other_files_is_refused(self):
        self.commit(**{"c1.json": "1"})
        self.commit(**{"d.json": "{}", "o.txt": "x"})
        counts = self.commit(**{"c2.json": "2"})
        with self.assertRaisesRegex(ValueError, "change only that file"):
            self.order(counts, counts)

    def test_uncommitted_edited_or_recommitted_is_refused(self):
        self.commit(**{"c1.json": "1"})
        head = self.commit(**{"o.txt": "x"})
        (self.repo / "d.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "not committed"):
            self.order(head, head)
        decl = self.commit(**{"d.json": "{}"})
        (self.repo / "d.json").write_text('{"e": 1}')
        with self.assertRaisesRegex(ValueError, "not the committed one"):
            self.order(decl, decl)
        (self.repo / "d.json").write_text("{}")
        again = self.commit(**{"d.json": '{"cells": []}'})
        with self.assertRaisesRegex(ValueError, "exactly one commit"):
            self.order(again, again)

    def test_the_pilot_follows_the_declaration_and_round_ones_counts(self):
        self.commit(**{"c1.json": "1"})
        self.commit(**{"d.json": "{}"})
        head = self.commit(**{"o.txt": "x"})
        r.check_declaration_at_pilot(self.repo, KEY, 2, head)

    def test_a_declaration_after_the_pilot_head_is_refused(self):
        self.commit(**{"c1.json": "1"})
        head = self.commit(**{"o.txt": "x"})
        self.commit(**{"d.json": "{}"})
        with self.assertRaisesRegex(ValueError, "not committed in the"):
            r.check_declaration_at_pilot(self.repo, KEY, 2, head)

    def test_a_pilot_before_round_ones_counts_is_refused(self):
        self.commit(**{"d.json": "{}"})
        head = self.commit(**{"c1.json": "1"})
        with self.assertRaisesRegex(ValueError, "not a descendant"):
            r.check_declaration_at_pilot(self.repo, KEY, 2, head)

    def test_every_counts_file_of_the_round_before_precedes(self):
        self.before = ["c1.json", "c1r.json"]
        self.commit(**{"c1.json": "1"})
        self.commit(**{"c1r.json": "r"})
        self.commit(**{"d.json": "{}"})
        counts = self.commit(**{"c2.json": "2"})
        self.order(counts, counts)

    def test_a_revision_committed_after_the_declaration_is_refused(self):
        self.before = ["c1.json", "c1r.json"]
        self.commit(**{"c1.json": "1"})
        self.commit(**{"d.json": "{}"})
        self.commit(**{"c1r.json": "r"})
        counts = self.commit(**{"c2.json": "2"})
        with self.assertRaisesRegex(ValueError, "c1r.json"):
            self.order(counts, counts)
        with self.assertRaisesRegex(ValueError, "c1r.json"):
            r.check_declaration_at_pilot(self.repo, KEY, 2, counts)

    def test_the_counts_files_are_those_of_the_engine_before(self):
        engine = types.SimpleNamespace(t=types.SimpleNamespace(
            files=lambda: ("a", "b")))
        with mock.patch.object(r, "engine_before", lambda key, n: engine):
            self.assertEqual(
                ORIGINAL_FILES(KEY, 2), ("a", "b"))

    def test_round_three_follows_round_twos_counts(self):
        self.commit(**{"c1.json": "1", "c2.json": "2"})
        self.before = ["c2.json"]
        with mock.patch.object(r, "declaration_file",
                               lambda key, n: self.repo / "d3.json"):
            self.commit(**{"d3.json": "{}"})
            counts = self.commit(**{"c3.json": "3"})
            r.check_declaration_order(self.repo, counts, KEY, 3, counts)

    def test_the_engine_checks_the_pilot_and_every_counts_commit(self):
        built, engine = r.declare(KEY, 2, dict(
            cells=tuple(CELLS[:1]), pairs=80, decision=DECISION))
        self.commit(**{"o.txt": "x"})
        head = self.git("rev-parse", "HEAD")
        with mock.patch.object(r, "check_declaration_at_pilot") as check, \
                mock.patch.object(tg.Grid, "pilot", return_value=0) as run:
            args = mock.Mock(repo=self.repo)
            self.assertEqual(engine.pilot(args), 0)
            check.assert_called_once_with(self.repo, KEY, 2, head)
            run.assert_called_once_with(args)
        with mock.patch.object(r, "check_declaration_at_pilot",
                               side_effect=ValueError("late")), \
                mock.patch.object(tg.Grid, "pilot") as run:
            with self.assertRaisesRegex(ValueError, "late"):
                engine.pilot(mock.Mock(repo=self.repo))
            run.assert_not_called()
        with mock.patch.object(tg.Grid, "check_pilot_settings"), \
                mock.patch.object(f, "repo_of_code",
                                  return_value=self.repo), \
                mock.patch.object(r, "check_declaration_at_pilot") as check:
            engine.check_pilot_settings({"checkout": {"head": "h" * 40}})
            check.assert_called_once_with(self.repo, KEY, 2, "h" * 40)
            with self.assertRaisesRegex(ValueError, "no checkout head"):
                engine.check_pilot_settings({})
        with mock.patch.object(tg.Grid, "counts_commit",
                               return_value="a" * 40) as run, \
                mock.patch.object(r, "check_declaration_order") as check:
            self.assertEqual(engine.counts_commit("repo", "cand", "p"),
                             "a" * 40)
        run.assert_called_once_with("repo", "cand", "p")
        check.assert_called_once_with("repo", "cand", KEY, 2, "a" * 40)
        with mock.patch.object(tg.Grid, "counts_commit",
                               return_value="a" * 40), \
                mock.patch.object(r, "check_declaration_order",
                                  side_effect=ValueError("late")):
            with self.assertRaisesRegex(ValueError, "late"):
                engine.counts_commit("repo", "cand", "p")


class Predeclare(unittest.TestCase):
    """`predeclare` of a round checks the declaration against the last
    stage of the round before, first."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.rows = [dict(case="c", size=1, protocol=True),
                     dict(case="c", size=10, protocol=True)]
        (self.root / "decisions.json").write_text(json.dumps(
            dict(workloads=self.rows)))
        self.classes = {1: "inconclusive", 10: "pass"}
        for target, value in (
                (r, ("engine_before", lambda key, n: FakeEngine())),
                (r, ("stage_reports", lambda engine, grid: dict(
                    inventory={}, first=dict(pairs=40, iterations={}),
                    stage1={("c", 1): report(0.01),
                            ("c", 10): report(0.01)}, stage2={}))),
                (tg, ("classify_row",
                      lambda w: self.classes[w["size"]]))):
            patch = mock.patch.object(target, *value)
            patch.start()
            self.addCleanup(patch.stop)

    def engine_of(self, cells, pairs=80):
        engine = r.Rounds.__new__(r.Rounds)
        engine.key, engine.number = KEY, 2
        engine.t = types.SimpleNamespace(names=lambda: list(cells),
                                         pairs=pairs)
        return engine

    def test_the_after_option_is_required(self):
        _, engine = r.declare(KEY, 2, dict(
            cells=tuple(CELLS[:1]), pairs=80, decision=DECISION))
        parser, _ = engine.parser()
        with contextlib.redirect_stderr(io.StringIO()), \
                self.assertRaises(SystemExit):
            parser.parse_args(["predeclare", "--grid", "g", "--output",
                               "o"])
        got = parser.parse_args(["predeclare", "--grid", "g", "--output",
                                 "o", "--after", "x"])
        self.assertEqual(got.after, Path("x"))
        # the other commands do not take it
        with contextlib.redirect_stderr(io.StringIO()), \
                self.assertRaises(SystemExit):
            parser.parse_args(["verify-counts", "--grid", "g", "--after",
                               "x"])

    def test_a_right_declaration_passes_and_dispatch_goes_on(self):
        engine = self.engine_of(["c-1"])
        engine.check_after(self.root)
        args = types.SimpleNamespace(action="predeclare", after=self.root)
        with mock.patch.object(tg.Grid, "dispatch",
                               return_value=0) as run:
            self.assertEqual(engine.dispatch(args), 0)
        run.assert_called_once_with(args)

    def test_a_wrong_declaration_is_refused_before_anything_else(self):
        args = types.SimpleNamespace(action="predeclare", after=self.root)
        for cells, pairs, regex in (
                (["c-1"], 100, "the rule gives 80"),
                (["c-1"], 40, "the rule gives 80"),
                (["c-10"], 80, "exactly"),
                (["c-1", "c-10"], 80, "exactly")):
            engine = self.engine_of(cells, pairs)
            with mock.patch.object(tg.Grid, "dispatch") as run:
                with self.assertRaisesRegex(ValueError, regex):
                    engine.dispatch(args)
            run.assert_not_called()
        # a subset of the open cells is refused, a superset too
        self.classes[10] = "inconclusive"
        for cells in (["c-1"], ["c-1", "c-10", "c-100"]):
            with self.assertRaisesRegex(ValueError, "exactly"):
                self.engine_of(cells).check_after(self.root)
        self.engine_of(["c-1", "c-10"]).check_after(self.root)

    def test_other_commands_do_not_check(self):
        engine = self.engine_of(["c-10"], 1)
        args = types.SimpleNamespace(action="verify-counts")
        with mock.patch.object(tg.Grid, "dispatch",
                               return_value=3) as run:
            self.assertEqual(engine.dispatch(args), 3)
        run.assert_called_once_with(args)


class StageFixture(unittest.TestCase):
    """`stage_reports` (unmocked) and the `replayed` of `Grid.replay` are
    made from one fixture and give `decisive_pairs` the same answer."""

    class Engine(FakeEngine):
        def __init__(self, extended):
            super().__init__()
            self.t.schema = lambda kind: "S-" + kind
            self.extended = extended
            self.rows = {}

        def replay_rows(self, root, inventory):
            return self.rows[inventory["name"]]

        def planned(self, stage1, first):
            return [["c", 1, 90]] if self.extended else []

    def make(self, extended):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        engine = self.Engine(extended)
        first_dir = root / "first"
        first_dir.mkdir()
        first = dict(schema="S-experiment", name="first", pairs=40,
                     iterations=dict(pairs_by_cell={"c-2": 30}))
        a.save(first_dir / "inventory.json", first)
        a.save(first_dir / "decisions.json", dict(workloads=[]))
        engine.rows["first"] = {("c", 1): report(0.5),
                                ("c", 2): report(0.02)}
        if not extended:
            return engine, first_dir, first, None, None
        ext_dir = root / "ext"
        ext_dir.mkdir()
        ext = dict(schema="S-extension", name="ext", grid="../first",
                   grid_inventory=a.seal(first_dir / "inventory.json"),
                   grid_decisions=a.seal(first_dir / "decisions.json"),
                   plan=[["c", 1, 90]])
        a.save(ext_dir / "inventory.json", ext)
        engine.rows["ext"] = {("c", 1): report(0.01)}
        return engine, ext_dir, first, ext, root

    def replayed(self, engine, first, ext):
        """What `Grid.replay` keeps of the stage (its `replayed`)."""
        stage1 = engine.rows["first"]
        if ext is None:
            return dict(inventory=first, first=first, stage1=stage1,
                        stage2={}, decisions={})
        return dict(inventory=ext, first=first, stage1=stage1,
                    stage2=engine.rows["ext"], decisions={})

    def test_a_single_stage_is_read_as_the_replay_keeps_it(self):
        engine, root, first, _, _ = self.make(False)
        found = r.stage_reports(engine, root)
        replayed = self.replayed(engine, first, None)
        self.assertEqual(found, {k: v for k, v in replayed.items()
                                 if k != "decisions"})
        names = ["c-1", "c-2"]
        self.assertEqual(r.decisive_pairs(engine, found, names),
                         r.decisive_pairs(engine, replayed, names))
        # c-2 has 30 pairs in the counts; c-1 the stage's 40
        self.assertEqual(r.decisive_pairs(engine, found, names), {
            "c-1": 120, "c-2": tg.second_stage_pairs(0.02, 30, 0.015,
                                                     120)})

    def test_an_extension_is_read_as_the_replay_keeps_it(self):
        engine, root, first, ext, _ = self.make(True)
        found = r.stage_reports(engine, root)
        replayed = self.replayed(engine, first, ext)
        self.assertEqual(found, {k: v for k, v in replayed.items()
                                 if k != "decisions"})
        names = ["c-1", "c-2"]
        self.assertEqual(r.decisive_pairs(engine, found, names),
                         r.decisive_pairs(engine, replayed, names))
        per = r.decisive_pairs(engine, found, names)
        # c-1 by the extension's report and its planned 90 pairs
        self.assertEqual(per["c-1"], tg.second_stage_pairs(
            0.01, 90, 0.015, 120))
        self.assertEqual(r.declared_pairs(engine, found, names)[0],
                         max(per.values()))

    def test_a_first_stage_with_a_second_stage_to_come_is_refused(self):
        engine, root, _, _, _ = self.make(False)
        engine.extended = True
        with self.assertRaisesRegex(ValueError, "second stage is still to "
                                    "come, name the second stage"):
            r.stage_reports(engine, root)

    def test_the_first_stage_of_an_extended_grid_is_not_the_last(self):
        engine, ext_dir, _, _, root = self.make(True)
        with self.assertRaisesRegex(ValueError, "still to come"):
            r.stage_reports(engine, root / "first")
        # the extension is accepted
        r.stage_reports(engine, ext_dir)

    def test_a_changed_first_stage_or_a_foreign_grid_is_refused(self):
        engine, ext_dir, _, _, root = self.make(True)
        (root / "first" / "decisions.json").write_text("{}")
        with self.assertRaisesRegex(ValueError, "changed first-stage"):
            r.stage_reports(engine, ext_dir)
        other, other_dir, _, _, _ = self.make(False)
        other.t.schema = lambda kind: "other-" + kind
        with self.assertRaisesRegex(ValueError, "not a stage of"):
            r.stage_reports(other, other_dir)


CAND = "c" * 40
ORIGINAL_FILES = r.previous_counts_files


def fake_engine(table, name, cells, pairs=80):
    return types.SimpleNamespace(
        t=types.SimpleNamespace(name=name, fixed_seconds=True, pairs=pairs,
                                counts=types.SimpleNamespace(name="x"),
                                names=lambda: list(cells)),
        replayed="replayed:" + name)


class Dispose(unittest.TestCase):
    """The rounds chain in the disposition (task37_dispose.read_shard)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.key = KEY
        self.table = g.name_of(self.key)
        self.names = list(g.PARTS[self.key])
        self.cell = self.names[0]
        self.calls = []
        self.engine = types.SimpleNamespace(
            t=types.SimpleNamespace(name=self.table, fixed_seconds=True,
                                    counts=types.SimpleNamespace(name="x")),
            h=types.SimpleNamespace(attempt_counts=lambda l, c: (1, 1)))
        self.ledger = self.root / "ledger"
        self.ledger.touch()
        self.records = []
        self.round1 = fake_engine(self.table, f.name_of(self.key),
                                  [self.cell])
        self.round2 = fake_engine(self.table, r.name_of(self.key, 2),
                                  [self.cell], 80)
        self.round3 = fake_engine(self.table, r.name_of(self.key, 3),
                                  [self.cell], 160)
        self.stages = {}
        self.pair_checks = []
        for target, name, value in (
                (d, "timing_engine", lambda key: self.engine),
                (d, "read_stage", self.stage),
                (d, "check_counts", lambda *args: None),
                (d, "check_declaration", lambda *args: None),
                (d, "check_round_declaration", self.declaration),
                (d, "round_declaration", lambda key, n: dict(
                    decision="decision-%d" % n)),
                (d, "pins_binding", lambda *args: {}),
                (d, "replay_timing", self.spy),
                (d, "ledger_attempts", self.attempts),
                (r, "check_pairs", self.pairs),
                (d31, "judged_attempts", lambda e, root: {"a1": root}),
                (tg, "Ledger", lambda path: types.SimpleNamespace(
                    records=self.records))):
            patch = mock.patch.object(target, name, value)
            patch.start()
            self.addCleanup(patch.stop)

    def stage(self, root, label, lineage):
        found = dict(
            root=Path(root), first_root=Path(root),
            inventory=dict(candidate=CAND, replaces=dict(grid="../main")),
            first_inventory={}, scaling=None, scaling_raw=None,
            differing=[], seals={}, plan={},
            final={n: "pass" for n in self.names},
            first={n: "pass" for n in self.names})
        found.update(self.stages.get(Path(root).name, {}))
        return found

    def declaration(self, key, number, stage, repo):
        self.calls.append(("declaration", key, number, repo))

    def spy(self, engine, root, repo, ledger, pilot=None,
            replaces_pilot=None):
        self.calls.append(("replay", engine.t.name, pilot, replaces_pilot))

    def attempts(self, engine, judged, repo, ledger):
        self.calls.append(("attempts", engine.t.name))
        return []

    def pairs(self, engine, found, names, pairs):
        self.pair_checks.append((engine.t.name, found, list(names), pairs))

    def classes(self, **named):
        """Stage directories by name: {stage: class of the cell}."""
        for name, cls in named.items():
            self.stages[name] = dict(
                final={self.cell: cls}, first={self.cell: cls})
        (self.root / "main").mkdir(exist_ok=True)

    def options(self, rounds=("f",), declared=None):
        opts = dict(timing={self.key: self.root / "main"},
                    ledger={self.key: self.ledger},
                    pilot={self.key: self.root / "pilot"}, followup={})
        opts["followup-pilot"] = {}
        keys = [self.key] + ["%s.%d" % (self.key, n)
                             for n in range(2, len(rounds) + 1)]
        for k, name in zip(keys, rounds):
            opts["followup"][k] = self.root / name
            opts["followup-pilot"][k] = self.root / ("p" + name)
        return opts

    def read(self, options, declared=2):
        engines = {f.name_of(self.key): self.round1}
        extra = {r.name_of(self.key, 2): self.round2,
                 r.name_of(self.key, 3): self.round3}
        extra = {k: v for k, v in extra.items()
                 if int(k[-1]) <= declared}
        late = []
        with mock.patch.object(d, "followup_engines", lambda: engines), \
                mock.patch.object(d, "round_engines", lambda: extra):
            held = d.read_shard(self.key, options, mock.Mock(), "repo", {},
                                late)
        return held, late

    def test_a_cell_is_judged_by_its_last_round(self):
        self.classes(f="inconclusive", f2="pass")
        self.stages["main"] = dict(
            final={n: "inconclusive" if n == self.cell else "pass"
                   for n in self.names},
            first={n: "inconclusive" if n == self.cell else "pass"
                   for n in self.names})
        held, late = self.read(self.options(("f", "f2")))
        row = held["cells"][self.cell]
        self.assertEqual((row["cls"], row["followup"]), ("pass", True))
        self.assertEqual(row["earlier"], ["inconclusive", "inconclusive"])
        late[0][1]()
        names = [x[1] for x in self.calls if x[0] == "replay"]
        self.assertEqual(names, [self.table, f.name_of(self.key),
                                 r.name_of(self.key, 2)])
        replays = [x for x in self.calls if x[0] == "replay"]
        self.assertEqual(replays[2][2:], ((self.root / "pf2").resolve(),
                                          None))
        # the pairs of round 2 are checked against round 1's replay
        # (the engine checked is the round before, the pairs round 2's)
        self.assertEqual(self.pair_checks, [(
            f.name_of(self.key), "replayed:" + f.name_of(self.key),
            [self.cell], 80)])
        self.assertIn(("declaration", self.key, 2, "repo"), self.calls)
        attempts = [x[1] for x in self.calls if x[0] == "attempts"]
        self.assertEqual(attempts, [self.table, f.name_of(self.key),
                                    r.name_of(self.key, 2)])

    def test_an_inconclusive_last_round_owes_an_attribution(self):
        self.classes(f="inconclusive", f2="inconclusive")
        self.stages["main"] = dict(
            final={n: "inconclusive" if n == self.cell else "pass"
                   for n in self.names},
            first={n: "inconclusive" if n == self.cell else "pass"
                   for n in self.names})
        held, _ = self.read(self.options(("f", "f2")))
        row = held["cells"][self.cell]
        failed, missing, owed = [], [], []
        d.judge_timing(self.cell, row, set(), failed, missing, owed)
        self.assertEqual((failed, owed), ([], ["attribution"]))

    def test_a_fail_of_an_earlier_round_still_decides(self):
        self.classes(f="fail", f2="pass")
        self.stages["main"] = dict(
            final={n: "inconclusive" if n == self.cell else "pass"
                   for n in self.names},
            first={n: "inconclusive" if n == self.cell else "pass"
                   for n in self.names})
        # round 1 failed, though round 2 passed: round 2 must be open in
        # round 1 to run, so a fail is refused as a chain
        with self.assertRaisesRegex(ValueError, "not all inconclusive"):
            self.read(self.options(("f", "f2")))
        # a first-stage fail of the last round decides
        self.classes(f="inconclusive", f2="pass")
        self.stages["f2"]["first"] = {self.cell: "fail"}
        self.stages["main"] = dict(
            final={n: "inconclusive" if n == self.cell else "pass"
                   for n in self.names},
            first={n: "inconclusive" if n == self.cell else "pass"
                   for n in self.names})
        held, _ = self.read(self.options(("f", "f2")))
        failed, missing, owed = [], [], []
        d.judge_timing(self.cell, held["cells"][self.cell], set(), failed,
                       missing, owed)
        self.assertEqual(failed, ["timing: an earlier stage failed"])

    def open_main(self):
        self.stages["main"] = dict(
            final={n: "inconclusive" if n == self.cell else "pass"
                   for n in self.names},
            first={n: "inconclusive" if n == self.cell else "pass"
                   for n in self.names})

    def test_a_declared_round_with_no_option_is_refused(self):
        self.classes(f="inconclusive")
        self.open_main()
        with self.assertRaisesRegex(ValueError, "declared and has no"):
            self.read(self.options(("f",)))
        with self.assertRaisesRegex(ValueError, "declared and has no"):
            self.read(self.options(()))

    def test_an_undeclared_round_is_refused(self):
        self.classes(f="inconclusive", f2="inconclusive",
                     f3="inconclusive")
        self.open_main()
        with self.assertRaisesRegex(ValueError, "matrix-4.3 .*not declared|"
                                    "round 3 .*not declared"):
            self.read(self.options(("f", "f2", "f3")), declared=2)

    def test_a_round_needs_the_rounds_before_it(self):
        self.classes(f="inconclusive", f2="inconclusive")
        self.open_main()
        options = self.options(("f", "f2"))
        del options["followup"][self.key]
        del options["followup-pilot"][self.key]
        with self.assertRaisesRegex(ValueError, "needs the rounds before"):
            self.read(options)
        options = self.options(("f", "f2", "f3"))
        del options["followup"]["matrix-4.2"]
        with self.assertRaisesRegex(ValueError, "declared and has no"):
            self.read(options, declared=3)

    def test_a_round_needs_its_pilot(self):
        self.classes(f="inconclusive", f2="inconclusive")
        self.open_main()
        options = self.options(("f", "f2"))
        del options["followup-pilot"]["matrix-4.2"]
        with self.assertRaisesRegex(ValueError, "needs --followup-pilot"):
            self.read(options)

    def test_a_cell_not_open_in_the_round_before_is_refused(self):
        self.classes(f="pass", f2="pass")
        self.open_main()
        # round 1 passed the cell, so round 2 had nothing to measure
        with self.assertRaisesRegex(ValueError, "not all inconclusive"):
            self.read(self.options(("f", "f2")))

    def test_the_cells_must_be_the_declared_rounds(self):
        self.classes(f="inconclusive", f2="inconclusive")
        self.open_main()
        self.stages["f2"]["final"] = {n: "inconclusive"
                                      for n in self.names[:2]}
        with self.assertRaisesRegex(ValueError, "not the declared round's"):
            self.read(self.options(("f", "f2")))

    def test_the_declaration_of_each_round_is_checked(self):
        self.classes(f="inconclusive", f2="inconclusive",
                     f3="inconclusive")
        self.open_main()
        self.read(self.options(("f", "f2", "f3")), declared=3)
        self.assertEqual(
            [x[2] for x in self.calls if x[0] == "declaration"], [2, 3])

    def test_each_rounds_pairs_are_checked_against_the_round_before(self):
        self.classes(f="inconclusive", f2="inconclusive",
                     f3="inconclusive")
        self.open_main()
        _, late = self.read(self.options(("f", "f2", "f3")), declared=3)
        late[0][1]()
        self.assertEqual(
            [(x[0], x[1], x[3]) for x in self.pair_checks],
            [(f.name_of(self.key), "replayed:" + f.name_of(self.key), 80),
             (r.name_of(self.key, 2),
              "replayed:" + r.name_of(self.key, 2), 160)])

    def test_a_pairs_mismatch_refuses_after_the_replays(self):
        self.classes(f="inconclusive", f2="inconclusive")
        self.open_main()
        _, late = self.read(self.options(("f", "f2")))
        with mock.patch.object(r, "check_pairs", side_effect=ValueError(
                "the round declares 80 pairs; the rule gives 100")):
            with self.assertRaisesRegex(ValueError, "the rule gives"):
                late[0][1]()
        self.assertEqual(
            [x[1] for x in self.calls if x[0] == "replay"],
            [self.table, f.name_of(self.key), r.name_of(self.key, 2)])
        self.assertEqual([x for x in self.calls if x[0] == "attempts"], [])

    def two_cells(self):
        """Round 1 measured two cells; both stayed inconclusive."""
        self.cell2 = self.names[1]
        self.round1.t.names = lambda: [self.cell, self.cell2]
        self.stages["main"] = dict(
            final={n: "inconclusive" if n in (self.cell, self.cell2)
                   else "pass" for n in self.names},
            first={n: "inconclusive" if n in (self.cell, self.cell2)
                   else "pass" for n in self.names})
        self.stages["f"] = dict(
            final={n: "inconclusive" for n in (self.cell, self.cell2)},
            first={n: "inconclusive" for n in (self.cell, self.cell2)})
        (self.root / "main").mkdir(exist_ok=True)

    def test_a_round_takes_exactly_the_cells_left_inconclusive(self):
        self.two_cells()
        both = [self.cell, self.cell2]
        self.round2.t.names = lambda: both
        self.stages["f2"] = dict(final={n: "pass" for n in both},
                                 first={n: "pass" for n in both})
        held, _ = self.read(self.options(("f", "f2")))
        self.assertEqual(held["cells"][self.cell]["cls"], "pass")

    def test_a_subset_of_the_open_cells_is_refused(self):
        self.two_cells()
        self.round2.t.names = lambda: [self.cell]
        self.stages["f2"] = dict(final={self.cell: "inconclusive"},
                                 first={self.cell: "inconclusive"})
        with self.assertRaisesRegex(ValueError, "not exactly the cells"):
            self.read(self.options(("f", "f2")))

    def test_a_superset_of_the_open_cells_is_refused(self):
        self.two_cells()
        extra = self.names[2]
        three = [self.cell, self.cell2, extra]
        self.round2.t.names = lambda: three
        self.stages["f2"] = dict(final={n: "inconclusive" for n in three},
                                 first={n: "inconclusive" for n in three})
        with self.assertRaisesRegex(ValueError, "not all inconclusive"):
            self.read(self.options(("f", "f2")))
        # a cell of the round before that passed
        self.stages["f"] = dict(
            final={self.cell: "inconclusive", self.cell2: "pass"},
            first={self.cell: "inconclusive", self.cell2: "pass"})
        self.round2.t.names = lambda: [self.cell, self.cell2]
        self.stages["f2"] = dict(
            final={n: "pass" for n in (self.cell, self.cell2)},
            first={n: "pass" for n in (self.cell, self.cell2)})
        with self.assertRaisesRegex(ValueError, "not all inconclusive"):
            self.read(self.options(("f", "f2")))

    def test_the_record_cites_each_rounds_decision(self):
        self.classes(f="inconclusive", f2="inconclusive",
                     f3="inconclusive")
        self.open_main()
        held, _ = self.read(self.options(("f", "f2", "f3")), declared=3)
        self.assertEqual(held["rounds"], [
            dict(round=2, table=r.name_of(self.key, 2), cells=[self.cell],
                 pairs=80, decision="decision-2"),
            dict(round=3, table=r.name_of(self.key, 3), cells=[self.cell],
                 pairs=160, decision="decision-3")])
        self.classes(f="pass")
        held, _ = self.read(self.options(("f",)), declared=1)
        self.assertEqual(held["rounds"], [])

    def test_the_decision_comes_from_the_declaration(self):
        with mock.patch.dict(r.DECLARED, {KEY: {2: dict(
                cells=(), pairs=1, decision="x")}}, clear=True):
            self.assertEqual(ORIGINAL_DECLARATION(KEY, 2)["decision"], "x")

    def ledger_run(self, declared=2, rounds=("f", "f2")):
        self.classes(f="inconclusive", f2="inconclusive",
                     f3="inconclusive")
        self.open_main()
        _, late = self.read(self.options(rounds), declared=declared)
        late[0][1]()

    def test_a_ledger_of_exactly_the_judged_tables_passes(self):
        self.records[:] = [dict(event="open", table=t) for t in (
            self.table, f.name_of(self.key), r.name_of(self.key, 2))] + [
            dict(event="torn"), dict(event="open")]
        self.ledger_run()

    def test_a_measured_round_whose_declaration_is_gone_is_refused(self):
        for table in (r.name_of(self.key, 3), self.table + "-followup4",
                      self.table + "-followup1", self.table + "-followup0"):
            self.records[:] = [dict(event="close", table=table)]
            with self.assertRaisesRegex(ValueError, "does not judge"):
                self.ledger_run()
        # another shard's tables are not this ledger's concern
        self.records[:] = [dict(event="open", table="task37-matrix-3-"
                                "followup5")]
        self.ledger_run()

    def test_round_one_alone_has_no_other_follow_up_in_its_ledger(self):
        self.classes(f="pass")
        self.records[:] = [dict(event="open", table=f.name_of(self.key))]
        _, late = self.read(self.options(("f",)), declared=1)
        late[0][1]()
        self.records[:] = [dict(event="open", table=r.name_of(self.key, 2))]
        _, late = self.read(self.options(("f",)), declared=1)
        with self.assertRaisesRegex(ValueError, "does not judge"):
            late[0][1]()

    def test_check_round_declaration_reads_each_counts_commit(self):
        stage = dict(inventory=dict(candidate=CAND, counts_commit="1" * 40),
                     first_inventory=dict(candidate="d" * 40,
                                          counts_commit="2" * 40))
        with mock.patch.object(r, "check_declaration_order") as run:
            ORIGINAL(KEY, 2, stage, "repo")
        self.assertEqual([x.args for x in run.call_args_list], [
            ("repo", CAND, KEY, 2, "1" * 40),
            ("repo", "d" * 40, KEY, 2, "2" * 40)])
        stage["inventory"].pop("counts_commit")
        with self.assertRaisesRegex(ValueError, "no counts commit"):
            ORIGINAL(KEY, 2, stage, "repo")

    def test_the_followup_options_take_a_shard_or_a_round(self):
        got = d.keyed_rounds(["matrix-4=/x", "matrix-4.2=/y"], "followup",
                             g.SHARD_KEYS)
        self.assertEqual(got, {"matrix-4": Path("/x"),
                               "matrix-4.2": Path("/y")})
        for bad in ("matrix-4.1=/x", "matrix-9.2=/x", "matrix-4.10=/x",
                    "x=/y", "matrix-4"):
            with self.assertRaises(ValueError, msg=bad):
                d.keyed_rounds([bad], "followup", g.SHARD_KEYS)
        with self.assertRaisesRegex(ValueError, "names matrix-4.2 twice"):
            d.keyed_rounds(["matrix-4.2=/x", "matrix-4.2=/y"], "followup",
                           g.SHARD_KEYS)

    def test_the_accessors_follow_the_round_engines(self):
        self.assertEqual(d.round_engines(), dict(r.GRIDS))
        self.assertEqual(d.declared_rounds(KEY), sorted(
            r.DECLARED.get(KEY, {})))
        engines = {r.name_of(KEY, 2): "E", r.name_of(KEY, 3): "F"}
        with mock.patch.object(d, "round_engines", lambda: engines):
            self.assertEqual(d.declared_rounds(KEY), [2, 3])
            self.assertEqual(d.declared_rounds("matrix-3"), [])

    def test_the_rounds_module_is_sealed_by_the_disposition(self):
        self.assertIn("task37_rounds.py", d.CODE)


ORIGINAL = d.check_round_declaration
ORIGINAL_DECLARATION = d.round_declaration


if __name__ == "__main__":
    unittest.main()
