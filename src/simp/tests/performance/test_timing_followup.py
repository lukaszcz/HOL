#!/usr/bin/env python3
"""A follow-up table of the shared timing grid: the cells it takes over from a
grid that left them inconclusive, their pairs, the replaced grid's replay and
the binding by its seals, the refusals, its own second stage and the evidence
family.

The rig is that of test_timing_grid.py: a toy table whose two stages are the
replaced grid, a toy follow-up of two of its cells, and the same stand-ins.
"""
import argparse
import contextlib
import io
import json
import math
from pathlib import Path
import unittest
from unittest.mock import patch

import acceptance as a
import test_timing_grid as ttg
import timing_grid as tg

CASES, SIZES = ttg.CASES, ttg.SIZES
FOLLOW = "d" * 40
# The cells the replaced grid leaves open: the control of the first has the
# interval GOOD (half log-width 0.01), that of the second, in the first stage
# of the replaced grid, NARROW (0.0257, outside the window, so the second
# stage remeasures the cell) and MID in its second stage.
CELL_A, CELL_B = (CASES[0], 100), (CASES[1], 1000)
CELLS = tuple("%s-%d" % k for k in (CELL_A, CELL_B))
NARROW, MID = (0.969, 1.02), (0.975, 1.025)


class Formula(unittest.TestCase):
    """The pairs of the second-stage rule, which the follow-up applies to the
    first stage of the grid it replaces."""

    def test_the_floor_is_twice_the_pairs(self):
        self.assertEqual(tg.second_stage_pairs(0.0, 20, 0.015, 120), 40)
        self.assertEqual(tg.second_stage_pairs(0.01, 20, 0.015, 120), 40)

    def test_the_count_is_rounded_up_to_tens(self):
        # 20 * (w / 0.015) ** 2 is 41.0 (and 40.0, 40.1 and 51.2).
        for wanted, expected in ((41.0, 50), (40.1, 50), (51.2, 60),
                                 (60.0, 60), (79.9, 80)):
            width = 0.015 * math.sqrt(wanted / 20)
            with self.subTest(wanted):
                self.assertEqual(
                    tg.second_stage_pairs(width, 20, 0.015, 120), expected)

    def test_the_cap_holds_whatever_the_width(self):
        self.assertEqual(tg.second_stage_pairs(0.05, 20, 0.015, 120), 120)
        self.assertEqual(tg.second_stage_pairs(math.inf, 20, 0.015, 120),
                         120)
        self.assertEqual(tg.second_stage_pairs(0.0, 70, 0.015, 120), 120)

    def test_the_pairs_scale_the_count(self):
        self.assertEqual(tg.second_stage_pairs(0.0253, 10, 0.015, 120), 30)
        self.assertEqual(tg.second_stage_pairs(0.0253, 20, 0.015, 120), 60)

    def test_the_width_is_the_larger_half_log_width_of_the_control(self):
        def result(cpu, wall):
            return dict(control=dict(metrics={
                "cpu": dict(paired_ratio_bootstrap_95_percent=cpu),
                "wall": dict(paired_ratio_bootstrap_95_percent=wall)}))
        self.assertAlmostEqual(
            tg.control_half_width(result([0.99, 1.01], [0.95, 1.06])),
            math.log(1.06 / 0.95) / 2)
        self.assertAlmostEqual(
            tg.control_half_width(result([0.95, 1.06], [0.99, 1.01])),
            math.log(1.06 / 0.95) / 2)
        self.assertEqual(
            tg.control_half_width(result(None, [0.99, 1.01])), math.inf)
        self.assertEqual(
            tg.control_half_width(result([0, 1.0], [0.99, 1.01])), math.inf)


class Tables(unittest.TestCase):
    OLD = tg.Table("toy", "TOY", CASES, "d.py", "c.json", fixed_seconds=True,
                   seed="s0", schedule="ramp", pairs=10,
                   seconds_by_case={CASES[0]: 1.0})

    def follow(self, **kw):
        options = dict(
            cells=CELLS, family="toy",
            replaces=tg.Replaces(tg.Grid(self.OLD)),
            fixed_seconds=True, seed="f0", pairs=20,
            seconds_by_case={CASES[0]: 1.0})
        options.update(kw)
        return tg.Table("toyf", "TOYF", CASES, "f.py", "f.json", **options)

    def test_the_cells_of_a_table_are_a_subset_in_order(self):
        table = self.follow()
        self.assertEqual(table.names(), list(CELLS))
        self.assertEqual(table.keys(), [CELL_A, CELL_B])
        self.assertEqual(len(table.every()), 12)
        self.assertEqual(self.OLD.cells, None)
        self.assertEqual(len(self.OLD.keys()), 12)
        self.assertEqual(table.seconds_map(),
                         {CELLS[0]: 1.0, CELLS[1]: 0.3})
        self.assertEqual(table.schema("grid"), "toyf-grid-v1")

    def test_unknown_or_repeated_cells_are_refused(self):
        for label, cells in (("unknown", (CELLS[0], "exclude_empty-7")),
                             ("other case", ("history_force-100",)),
                             ("repeated", (CELLS[0], CELLS[0])),
                             ("none", ())):
            with self.subTest(label), self.assertRaises(ValueError):
                self.follow(cells=cells)

    def test_the_family_is_the_name_unless_it_is_given(self):
        self.assertEqual(self.OLD.family, "toy")
        self.assertEqual(self.follow(family=None).family, "toyf")
        self.assertEqual(self.follow().family, "toy")
        with self.assertRaisesRegex(ValueError, "invalid family"):
            self.follow(family="../x")

    def test_a_follow_up_is_a_replaced_tables_cells_under_its_conditions(self):
        for label, kw in (
                ("no cells", dict(cells=None)),
                ("baseline", dict(baseline="b" * 40)),
                ("target", dict(target=0.02)),
                ("cap", dict(max_pairs=100)),
                ("pairs", dict(pairs=10)),
                ("pairs not twice", dict(pairs=30)),
                ("seconds", dict(seconds_by_case={})),
                ("seconds of a case", dict(seconds=0.5,
                                           seconds_by_case={CASES[0]: 1.0})),
                ("same seed", dict(seed="s0")),
                ("seed of the second stage", dict(seed="s0-ext")),
                ("no seed", dict(seed=None, require_seed=False))):
            with self.subTest(label), self.assertRaises(ValueError):
                self.follow(**kw)

    def test_a_follow_up_is_of_cells_of_the_table_it_replaces(self):
        small = tg.Table("toy", "TOY", CASES[:1], "d.py", "c.json",
                         fixed_seconds=True, seed="s0", schedule="ramp",
                         pairs=10, seconds_by_case={CASES[0]: 1.0})
        with self.assertRaisesRegex(ValueError, "cells of the table it "
                                    "replaces"):
            self.follow(replaces=tg.Replaces(tg.Grid(small)))

    def test_a_replaces_is_a_replaces(self):
        with self.assertRaisesRegex(ValueError, "malformed replaces"):
            self.follow(replaces=self.OLD)
        with self.assertRaisesRegex(ValueError, "unknown replacement"):
            tg.Replaces(self.OLD, "failed")

    def test_a_replaces_holds_the_engine_of_the_table_not_the_table(self):
        with self.assertRaisesRegex(ValueError, "malformed replaces"):
            tg.Replaces(self.OLD)
        engine = tg.Grid(self.OLD)
        replaces = tg.Replaces(engine)
        self.assertIs(replaces.engine, engine)
        self.assertIs(replaces.table, self.OLD)

    def test_the_seed_of_the_follow_up_may_end_in_ext_of_its_own(self):
        self.assertEqual(self.follow(seed="f0-x").seed, "f0-x")


class Rig(ttg.Rig):
    """The replaced grid (toy, 10 pairs, 12 cells, two of them inconclusive
    after its second stage, `replaced`, which remeasures the second of them
    after the first stage `replaced-1`) and a follow-up table (toyf, 20 pairs
    at the least) of those two."""
    pairs, samples = 10, 3
    OPEN = (CELL_A, CELL_B)

    def setUp(self):
        super().setUp()
        self.fdriver = self.root / "toyf_grid.py"
        self.fdriver.write_text("# the toy follow-up driver\n")
        self.fcounts = self.repo / "toyf_iterations.json"
        self.fpilot = self.root / "followup-pilot"
        self.between, self.follow_blob = [], {}
        # The stand-in analyses of the replaced grid (layout seed s0) and of
        # the follow-up (f0) are separate, as the replay of the first
        # must not follow what a test sets for the second.
        self.old_control, self.old_candidate = (self.mid_control,
                                                self.wide_when_open)
        self.new_control, self.new_candidate = (self.mid_control,
                                                self.wide_when_open)
        self.control = lambda c, s, pairs, seed: (
            self.new_control if str(seed).startswith("f") else
            self.old_control)(c, s, pairs, seed)
        self.candidate = lambda c, s, pairs, seed: (
            self.new_candidate if str(seed).startswith("f") else
            self.old_candidate)(c, s, pairs, seed)
        self.replaced1, status, _ = self.first(name="replaced-1")
        self.assertEqual(status, 2)
        self.replaced = self.second_stage(self.replaced1, "replaced")
        self.ftable = self.make_followup()
        self.fgrid = tg.Grid(self.ftable)
        self.runs.clear()
        self.launched.clear()

    def second_stage(self, grid, name):
        """The second stage of a first stage (the replaced grid, the TASK30
        grid being a grid of two stages)."""
        out = self.root / name
        code, text = self.go(self.argv(
            "extend", out, "--grid", str(grid), "--authorize-measurements"))
        self.assertEqual(code, 2, text)
        self.assertIn("PLAN", text)
        self.assertTrue(self.load(out / "inventory.json")["plan"])
        return out

    def two_stages(self, name, extra=()):
        """Another replaced grid, both stages, as the stand-ins now are."""
        grid, status, _ = self.first(name=name + "-1", extra=extra)
        self.assertEqual(status, 2)
        return self.second_stage(grid, name)

    def mid_control(self, case, size, pairs, seed):
        if (case, size) != CELL_B:
            return ttg.GOOD
        return NARROW if pairs < 30 else MID

    def wide_when_open(self, case, size, pairs, seed):
        return ttg.WIDE if (case, size) in self.OPEN else ttg.GOOD

    def make_followup(self, **kw):
        options = dict(
            cells=CELLS, family="toy", replaces=tg.Replaces(self.grid),
            root=self.root, seconds=0.3, seconds_by_case={CASES[0]: ttg.LONG},
            fixed_seconds=True, schedule="warmup", pairs=2 * self.pairs,
            samples=self.samples, seed="f0", tree="src",
            sources=ttg.SOURCES, sealed=ttg.SEALED, home=self.sealed_dir,
            ledger=self.attempts)
        options.update(kw)
        return tg.Table("toyf", "TOYF", CASES, self.fdriver, self.fcounts,
                        **options)

    # Stand-ins for the second commit ---------------------------------

    def fake_blob(self, repo, rev, path):
        if path == self.fcounts.name:
            if len(rev) != 40:
                raise ValueError("unknown revision: " + rev)
            return a.git(repo, "hash-object", str(self.fcounts)) \
                if self.fcounts.exists() else None
        if rev == FOLLOW:
            return self.follow_blob.get(path) or super().fake_blob(
                repo, ttg.CANDIDATE, path)
        return super().fake_blob(repo, rev, path)

    def fake_difference(self, repo, baseline, candidate, tree):
        if baseline == ttg.CANDIDATE:
            return sorted(self.between)
        return super().fake_difference(repo, baseline, candidate, tree)

    # Commands ---------------------------------------------------------

    def fgo(self, argv):
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = self.fgrid.execute(argv)
        return code, out.getvalue()

    def pilot(self):
        code, _ = self.fgo(["pilot", "--output", str(self.fpilot),
                            "--repo", str(self.repo),
                            "--authorize-measurements"])
        self.assertEqual(code, 0)

    def over(self, *extra):
        return ["--replaces", str(self.replaced), "--replaces-pilot",
                str(self.pilot_dir), *extra]

    def predeclare(self, *extra, output=None):
        return self.fgo(["predeclare", "--grid", str(self.fpilot),
                         "--output", str(output or self.fcounts),
                         "--repo", str(self.repo), *self.over(), *extra])

    def declare(self):
        self.pilot()
        code, _ = self.predeclare()
        self.assertEqual(code, 0)

    def run_followup(self, name="followup", *extra, candidate=FOLLOW):
        out = self.root / name
        code, text = self.fgo([
            "run", "--output", str(out), "--repo", str(self.repo),
            "--pilot", str(self.fpilot), "--candidate", candidate,
            "--authorize-measurements", *self.over(), *extra])
        return out, code, text

    def extend_followup(self, grid, name="followup-ext", *extra):
        out = self.root / name
        code, text = self.fgo([
            "extend", "--grid", str(grid), "--output", str(out), "--repo",
            str(self.repo), "--pilot", str(self.fpilot),
            "--authorize-measurements", *extra])
        return out, code, text

    def replay_followup(self, out, *extra):
        return self.fgo(["replay", "--output", str(out), "--repo",
                         str(self.repo), "--pilot", str(self.fpilot),
                         "--replaces-pilot", str(self.pilot_dir), *extra])

    def sealed_commands(self, out):
        """The commands that bind by the seals, as argument lists."""
        return {
            "verify-counts": ["verify-counts", "--grid", str(self.fpilot),
                              "--repo", str(self.repo), *self.over()],
            "run": ["run", "--output", str(self.root / "late"), "--repo",
                    str(self.repo), "--pilot", str(self.fpilot),
                    "--candidate", FOLLOW, "--authorize-measurements",
                    *self.over()],
            "extend": ["extend", "--grid", str(out), "--output",
                       str(self.root / "late-ext"), "--repo",
                       str(self.repo), "--pilot", str(self.fpilot),
                       "--authorize-measurements"]}

    def load(self, path):
        return json.loads(Path(path).read_text())


class Counts(Rig):
    def test_the_pilot_measures_only_the_cells_of_the_table(self):
        self.pilot()
        found = self.load(self.fpilot / "inventory.json")
        self.assertEqual(["%s-%d" % (r["case"], r["size"])
                          for r in found["runs"]], list(CELLS))
        self.assertEqual(found["schema"], "toyf-pilot-v1")
        self.assertEqual(len(self.launched), 2)
        self.assertEqual(sorted(self.load(self.fpilot / "variability.json")),
                         sorted(CELLS))

    def test_predeclare_records_the_pairs_derived_from_the_replaced_grid(self):
        self.declare()
        counts = self.load(self.fcounts)
        self.assertEqual(counts["schema"], "toyf-iterations-v1")
        self.assertEqual(sorted(counts["iterations"]), sorted(CELLS))
        # 10 pairs in the replaced first stage: control half widths 0.01
        # (the floor, 20) and 0.0253 (30).
        self.assertEqual(counts["pairs_by_cell"],
                         {CELLS[0]: 20, CELLS[1]: 30})
        self.assertEqual(counts["pairs"], 20)
        self.assertEqual(counts["schedule"], "warmup")
        self.assertEqual(counts["seconds"], {CELLS[0]: 1.0, CELLS[1]: 0.3})
        # The path of the replaced grid from the pilot, the seals of every
        # file the binding reads (both stages) and the open cells.
        self.assertEqual(counts["replaces"], dict(
            grid="../replaced", open=sorted(CELLS), files={
                name: a.seal(self.replaced / name)
                for name in ("inventory.json", "decisions.json",
                             "../replaced-1/inventory.json",
                             "../replaced-1/decisions.json")},
            code=self.fgrid.replay_code()))
        # The seals of the code the replay depended on.
        self.assertTrue({"timing_grid.py", "acceptance.py", "summarize.py",
                         "audit_evidence.py", "task30_pins.py",
                         self.counts.name} <= set(counts["replaces"]["code"]))
        self.assertEqual(counts["layout_seed"], "f0")
        code, text = self.fgo(["verify-counts", "--grid", str(self.fpilot),
                               "--repo", str(self.repo), *self.over()])
        self.assertEqual((code, text.splitlines()[-1]),
                         (0, "TOYF counts match their pilot"))

    def test_the_pairs_come_from_the_first_stage_control_of_the_cell(self):
        # The rule reads the develop/develop control of the first stage and
        # the pairs of that stage, however the grid replaced went on.
        self.old_control = lambda c, s, pairs, seed: (
            ttg.WIDE if (c, s) == CELL_A and pairs < 40 else ttg.GOOD)
        self.replaced = self.two_stages("replaced-2")
        self.declare()
        self.assertEqual(self.load(self.fcounts)["pairs_by_cell"],
                         {CELLS[0]: 120, CELLS[1]: 20})

    def test_counts_with_other_pairs_are_refused(self):
        self.declare()
        for label, pairs in (("lower", {CELLS[0]: 20, CELLS[1]: 20}),
                             ("higher", {CELLS[0]: 40, CELLS[1]: 30}),
                             ("a cell less", {CELLS[0]: 20})):
            with self.subTest(label):
                self.fcounts.write_text(json.dumps(dict(
                    self.load(self.fcounts), pairs_by_cell=pairs)))
                with self.assertRaisesRegex(
                        ValueError, "pairs or the replaced grid of the "
                        "counts differ"):
                    self.fgrid.check_counts(self.fpilot, self.fcounts)
                self.declare_followup_again()

    def test_a_replaced_grid_that_is_not_a_sibling_is_named(self):
        self.declare()
        counts = self.load(self.fcounts)
        counts["replaces"]["grid"] = "elsewhere/replaced"
        self.fcounts.write_text(json.dumps(counts))
        with self.assertRaisesRegex(
                ValueError, "must stay siblings, as in the evidence layout"):
            self.fgrid.check_counts(self.fpilot, self.fcounts)

    def declare_followup_again(self):
        self.fcounts.unlink()
        self.assertEqual(self.predeclare()[0], 0)

    def test_counts_of_another_replaced_grid_are_refused(self):
        self.declare()
        self.replaced = self.two_stages("replaced-again")
        with self.assertRaisesRegex(
                ValueError, "replaced grid changed since predeclare"):
            self.fgo(["verify-counts", "--grid", str(self.fpilot),
                      "--repo", str(self.repo), *self.over()])

    def test_predeclare_needs_the_replaced_grid_and_its_pilot(self):
        self.pilot()
        for argv in (
                ["predeclare", "--grid", str(self.fpilot), "--output",
                 str(self.fcounts), "--repo", str(self.repo)],
                ["predeclare", "--grid", str(self.fpilot), "--output",
                 str(self.fcounts), "--repo", str(self.repo),
                 "--replaces", str(self.replaced)]):
            with self.subTest(argv[-1]), self.assertRaisesRegex(
                    ValueError, "needs --replaces"):
                self.fgo(argv)
        self.assertFalse(self.fcounts.exists())

    def test_a_grid_that_is_not_the_replaced_one_gives_no_counts(self):
        # The cells are the open cells of the grid replaced, no others.
        self.old_candidate = lambda c, s, pairs, seed: (
            ttg.WIDE if (c, s) == CELL_A else ttg.GOOD)
        self.replaced = self.two_stages("replaced-one")
        self.pilot()
        with self.assertRaisesRegex(
                ValueError, "follow-up cells differ from the open cells"):
            self.predeclare()
        self.assertFalse(self.fcounts.exists())


class Run(Rig):
    def setUp(self):
        super().setUp()
        self.declare()
        self.committed_counts = True

    def test_the_cells_run_with_their_pairs_in_the_family_of_the_ledger(self):
        out, code, text = self.run_followup()
        self.assertEqual(code, 2, text)
        self.assertEqual(
            [(o["case"][0], o["size"][0], o["pairs"]) for o in self.runs],
            [(*CELL_A, 20), (*CELL_B, 30)])
        self.assertEqual({o["layout_seed"] for o in self.runs}, {"f0"})
        self.assertEqual({o["batch_schedule"] for o in self.runs},
                         {"warmup"})
        inventory = self.load(out / "inventory.json")
        self.assertEqual(inventory["schema"], "toyf-experiment-v1")
        self.assertEqual((inventory["pairs"], inventory["candidate"]),
                         (20, FOLLOW))
        self.assertEqual([r.get("pairs") for r in inventory["runs"]],
                         [None, 30])
        # The replaced grid's fields are named as its own, the follow-up's
        # seed and counts seal beside them.
        first = self.load(self.replaced1 / "inventory.json")
        self.assertEqual(inventory["replaces"], dict(
            grid="../replaced",
            replaced_inventory=a.seal(self.replaced / "inventory.json"),
            replaced_decisions=a.seal(self.replaced / "decisions.json"),
            replaced_seed="s0", replaced_counts=first["iterations_seal"],
            followup_seed="f0",
            followup_counts=inventory["iterations_seal"]))
        self.assertNotEqual(inventory["iterations_seal"],
                            first["iterations_seal"])
        self.assertIn(("toy", FOLLOW), self.kept)
        records = self.ledger()
        self.assertEqual({r["output"] for r in records[-2:]},
                         {str(out)})
        self.assertEqual(records[-2]["counts_file"], "toyf_iterations.json")
        # The two stages of the replaced grid and this one.
        self.assertEqual(len({r["attempt"] for r in self.ledger()}), 3)
        self.assertEqual([r["table"] for r in records[-2:]], ["toyf"] * 2)

    def test_the_decision_is_that_of_the_follow_up_cells_alone(self):
        # The candidate is as wide as in the replaced grid, so the follow-up
        # is inconclusive again: it blocks, whatever the rest was.
        out, code, text = self.run_followup()
        decisions = self.load(out / "decisions.json")
        self.assertEqual((code, decisions["status"]), (2, "inconclusive"))
        self.assertEqual(decisions["schema"], "toyf-grid-v1")
        self.assertEqual(len(decisions["workloads"]), 2)
        self.assertIn("TOYF grid: inconclusive (pass 0, fail 0, "
                      "inconclusive 2", text)
        self.assertIn("INCONCLUSIVE exclude_empty-100", text)

    def settled(self, ci_a=ttg.GOOD, ci_b=ttg.GOOD):
        self.new_candidate = lambda c, s, pairs, seed: {
            CELL_A: ci_a, CELL_B: ci_b}.get((c, s), ttg.GOOD)

    def test_a_follow_up_writes_no_final_decision(self):
        # The disposition step owns final.json; the follow-up decides its
        # own cells and replays.
        self.settled()
        out, code, text = self.run_followup()
        self.assertEqual(code, 0, text)
        self.assertFalse((out / "final.json").exists())
        self.assertNotIn("with the follow-up", text)
        code, text = self.replay_followup(out)
        self.assertEqual(code, 0, text)
        self.assertFalse((out / "final.json").exists())

    def test_a_follow_up_fail_is_a_fail(self):
        self.settled(ci_b=(1.04, 1.08))
        out, code, text = self.run_followup()
        self.assertEqual(code, 1, text)
        self.assertEqual(self.load(out / "decisions.json")["status"], "fail")
        self.assertEqual(self.replay_followup(out)[0], 1)

    def test_the_replay_replays_the_replaced_grid_too(self):
        self.settled()
        out, code, _ = self.run_followup()
        code, text = self.replay_followup(out)
        self.assertEqual(code, 0)
        self.assertEqual(
            text.count("TOY two-stage archives and decisions replayed"), 1)
        self.assertIn("TOYF archives and decisions replayed: pass", text)
        # A cell of the replaced grid that was changed breaks the follow-up.
        with patch.object(tg.bundle, "unpack", self.broken_unpack(
                "replaced")), self.assertRaises(Exception):
            self.replay_followup(out)

    def broken_unpack(self, folder):
        real = tg.bundle.unpack

        def unpack(archive, output):
            if folder in Path(archive).parts[-2:-1]:
                raise ValueError("changed archive")
            return real(archive, output)
        return unpack

    def test_the_replay_needs_the_pilot_of_the_replaced_grid(self):
        self.settled()
        out, code, _ = self.run_followup()
        with self.assertRaisesRegex(ValueError, "needs --replaces-pilot"):
            self.fgo(["replay", "--output", str(out), "--repo",
                      str(self.repo), "--pilot", str(self.fpilot)])

    def test_a_replaced_grid_that_changed_since_is_refused(self):
        self.settled()
        out, code, _ = self.run_followup()
        decisions = self.load(self.replaced / "decisions.json")
        decisions["status"] = "fail"
        (self.replaced / "decisions.json").write_text(json.dumps(decisions))
        with self.assertRaisesRegex(ValueError, "changed TOY decisions"):
            self.replay_followup(out)

    def test_an_only_run_is_a_diagnostic_subset_with_no_decision(self):
        out, code, text = self.run_followup("part", "--only", CELLS[1])
        self.assertEqual(code, 2)
        self.assertFalse((out / "decisions.json").exists())
        self.assertEqual([(o["case"][0], o["size"][0], o["pairs"])
                          for o in self.runs], [(*CELL_B, 30)])
        self.assertEqual(self.ledger()[-1]["status"], "partial")


class Refusals(Rig):
    """What `run --replaces` refuses, before an attempt opens."""

    def setUp(self):
        super().setUp()
        self.declare()

    def refused(self, pattern, name="refused", *extra):
        before = len(self.ledger())
        self.runs.clear()
        with self.assertRaisesRegex(ValueError, pattern):
            self.run_followup(name, *extra)
        self.assertEqual((self.runs, len(self.ledger())), ([], before))
        self.assertFalse((self.root / name).exists())

    def test_a_run_without_the_grid_it_replaces_is_refused(self):
        with self.assertRaisesRegex(ValueError, "needs --replaces GRID"):
            self.fgo(["run", "--output", str(self.root / "x"), "--repo",
                      str(self.repo), "--pilot", str(self.fpilot),
                      "--candidate", FOLLOW, "--authorize-measurements",
                      "--replaces-pilot", str(self.pilot_dir)])
        self.assertEqual(self.runs, [])

    def test_a_table_that_replaces_nothing_takes_no_grid(self):
        for argv in (
                ["run", "--output", str(self.root / "x"), "--repo",
                 str(self.repo), "--pilot", str(self.pilot_dir),
                 "--candidate", CANDIDATE_OTHER,
                 "--authorize-measurements", "--replaces",
                 str(self.replaced)],
                ["extend", "--grid", str(self.replaced1), "--output",
                 str(self.root / "x"), "--repo", str(self.repo), "--pilot",
                 str(self.pilot_dir), "--authorize-measurements",
                 "--replaces-pilot", str(self.pilot_dir)],
                ["replay", "--output", str(self.replaced), "--repo",
                 str(self.repo), "--pilot", str(self.pilot_dir),
                 "--replaces-pilot", str(self.pilot_dir)]):
            with self.subTest(argv[0]), self.assertRaisesRegex(
                    ValueError, "TOY replaces no grid"):
                self.go(argv)

    def other_replaced(self, open_cells):
        """Another replaced grid, with these cells open."""
        self.old_candidate = lambda c, s, pairs, seed: (
            ttg.WIDE if (c, s) in open_cells else ttg.GOOD)
        self.replaced = self.two_stages("replaced-other")

    def refused_by_predeclare(self, pattern):
        """The counts of another replaced grid cannot be made: the open cells
        are those of the grid, which `predeclare` replays."""
        self.fcounts.unlink()
        with self.assertRaisesRegex(ValueError, pattern):
            self.predeclare()
        self.assertFalse(self.fcounts.exists())

    def test_other_cells_than_the_open_ones_are_refused(self):
        self.other_replaced({CELL_A, (CASES[1], 0)})
        self.refused_by_predeclare("follow-up cells differ from the open "
                                   "cells")

    def test_fewer_cells_than_the_open_ones_are_refused(self):
        self.other_replaced({CELL_A})
        self.refused_by_predeclare("follow-up cells differ from the open "
                                   "cells")

    def test_more_cells_than_the_open_ones_are_refused(self):
        self.other_replaced({CELL_A, CELL_B, (CASES[1], 0)})
        self.refused_by_predeclare("follow-up cells differ from the open "
                                   "cells")

    def test_a_run_against_another_replaced_grid_than_the_counts_is_refused(
            self):
        # Same cells open, another grid: the seals of the counts differ.
        self.other_replaced({CELL_A, CELL_B})
        self.refused("replaced grid changed since predeclare: "
                     "inventory.json")

    def test_sources_other_than_the_replaced_grids_are_refused(self):
        # The pin of the follow-up accepts a blob of a file that the replaced
        # grid had at another (it, too, pinned).
        pins = {"src/one.sml": dict(blob="f" * 40, reason="A change.")}
        self.refused_with_pins(pins)

    def refused_with_pins(self, pins):
        self.differ = {"src/one.sml"}
        self.table.pinned = pins
        self.replaced = self.two_stages("replaced-pinned")
        self.fgrid = tg.Grid(self.make_followup(pinned={
            "src/one.sml": dict(blob="e" * 40, reason="Another change.")}))
        self.follow_blob = {"src/one.sml": "e" * 40}
        self.fcounts.unlink()
        self.assertEqual(self.predeclare()[0], 0)
        self.refused("candidate sources differ from the replaced grid's")

    def test_the_same_sources_are_accepted(self):
        pins = {"src/one.sml": dict(blob="f" * 40, reason="A change.")}
        self.differ = {"src/one.sml"}
        self.table.pinned = pins
        self.replaced = self.two_stages("replaced-pinned")
        self.fgrid = tg.Grid(self.make_followup(pinned=pins))
        self.fcounts.unlink()
        self.assertEqual(self.predeclare()[0], 0)
        self.follow_blob = {"src/one.sml": "f" * 40}
        out, code, text = self.run_followup()
        self.assertEqual(code, 2, text)

    def test_a_candidate_that_moved_the_tree_outside_the_harness_is_refused(
            self):
        self.between = [["M", "src/simp/src/simpLib.sml"]]
        self.refused("outside the performance area and the sealed files: "
                     "src/simp/src/simpLib.sml")
        self.between = [["M", "src/simp/tests/performance/MATRIX.md"],
                        ["A", "src/simp/tests/performance/x_iterations.json"]]
        out, code, text = self.run_followup("allowed")
        self.assertEqual(code, 2, text)

    def test_the_sealed_files_may_differ_wherever_they_are(self):
        # Sealed files in the repository: a sealed file outside the
        # performance area (as run_paired.py is) is the table's own code.
        # The names are those of the code's repository (here `root`), not
        # of the checkout a command is pointed at, and do not depend on the
        # files being there.
        table = self.make_followup(home=self.root / "area")
        self.fgrid = tg.Grid(table)
        names = {"area/one.txt", "area/two.txt", "toyf_grid.py"}
        self.assertEqual(self.fgrid.sealed_paths(), names)
        self.assertFalse((self.root / "area").exists())
        self.fgrid.replaced = dict(first=dict(
            candidate=ttg.CANDIDATE, layout_seed="s0", sources=None,
            baseline=a.BASE))
        inventory = dict(
            replaces=1, layout_seed="f0", candidate=FOLLOW,
            sources=None)
        other = self.root / "another-checkout"
        with patch.object(self.fgrid, "replaces_record",
                          lambda root, found: 1):
            for repo in (self.repo, other):
                with self.subTest(repo):
                    self.between = [["M", "area/one.txt"]]
                    self.fgrid.check_replaced(inventory, self.root, repo)
                    self.between = [["M", "area/three.txt"]]
                    with self.assertRaisesRegex(ValueError,
                                                "area/three.txt"):
                        self.fgrid.check_replaced(inventory, self.root,
                                                  repo)

    def test_a_sealed_file_outside_the_repository_is_refused(self):
        table = self.make_followup(home=self.root / "area", root=self.repo)
        with self.assertRaisesRegex(ValueError, "outside the repository"):
            tg.Grid(table).sealed_paths()

    def test_a_reused_seed_is_refused(self):
        # The table names a seed the replaced table no longer has, but the
        # grid it replaces was drawn with it.
        self.table.seed = "s9"
        self.fgrid = tg.Grid(self.make_followup(seed="s0"))
        self.fcounts.unlink()
        self.assertEqual(self.predeclare()[0], 0)
        self.refused("layout seed of the follow-up was drawn by the "
                     "replaced grid")

    def test_the_seed_of_the_replaced_second_stage_is_taken_too(self):
        self.table.seed = "s9"
        self.fgrid = tg.Grid(self.make_followup(seed="s0-ext"))
        self.fcounts.unlink()
        self.assertEqual(self.predeclare()[0], 0)
        self.refused("layout seed of the follow-up was drawn")

    def test_counts_bound_to_other_sealed_files_are_refused(self):
        value = self.load(self.fcounts)
        value["sealed"] = dict(value["sealed"], **{"one.txt": dict(
            bytes=1, sha256="0" * 64)})
        self.fcounts.write_text(json.dumps(value))
        self.refused("the counts are bound to other sealed files")

    def test_a_schedule_other_than_the_counts_is_refused(self):
        self.ftable.schedule = "ramp"
        self.refused("the schedule of the counts differs from the table's")

    def frewrite(self, **kw):
        self.fcounts.write_text(json.dumps(dict(self.load(self.fcounts),
                                                **kw)))

    def test_counts_with_other_pairs_are_refused_by_a_run(self):
        self.frewrite(pairs_by_cell={CELLS[0]: 20, CELLS[1]: 40})
        self.refused("pairs or the replaced grid of the counts differ")

    def test_counts_without_pairs_per_cell_are_refused(self):
        value = self.load(self.fcounts)
        del value["pairs_by_cell"]
        self.fcounts.write_text(json.dumps(value))
        self.refused("predeclared counts do not match the table")

    def test_a_grid_of_another_baseline_is_not_replaced(self):
        replaced = tg.Grid(self.make_table())
        self.ftable.baseline = "b" * 40
        self.assertEqual(replaced.t.baseline, a.BASE)
        self.refused("baseline")

    def test_pairs_are_twice_the_first_stage_of_the_replaced_grid(self):
        self.ftable.pairs = 30
        self.frewrite(pairs=30)
        self.refused("pairs of the table are not twice")


CANDIDATE_OTHER = "e" * 40


class Second(Rig):
    """The follow-up's own second stage, from its own control."""

    def setUp(self):
        super().setUp()
        self.declare()
        # The control of the second cell is wide until it has 60 pairs; its
        # candidate is wide too, until the control is valid.
        self.new_control = lambda c, s, pairs, seed: (
            ttg.WIDE if (c, s) == CELL_B and pairs < 60 else ttg.GOOD)
        self.new_candidate = lambda c, s, pairs, seed: ttg.GOOD

    def test_a_cell_the_control_leaves_open_is_remeasured(self):
        out, code, text = self.run_followup()
        self.assertEqual(code, 2, text)
        self.runs.clear()
        ext, code, text = self.extend_followup(out)
        self.assertEqual(code, 0, text)
        # From the control alone: the half width 0.0549 of 30 pairs.
        self.assertIn('PLAN 1 cells: [["exclude_missing", 1000, 120]]', text)
        options, = self.runs
        self.assertEqual((options["layout_seed"], options["pairs"]),
                         ("f0-ext", 120))
        self.assertEqual(options["batch_schedule"], "warmup")
        inventory = self.load(ext / "inventory.json")
        self.assertEqual(inventory["schema"], "toyf-extension-v1")
        self.assertEqual(inventory["replaces"]["grid"], "../replaced")
        self.assertEqual(inventory["plan"], [[CELL_B[0], CELL_B[1], 120]])
        self.assertEqual(self.load(ext / "decisions.json")["status"], "pass")
        self.assertFalse((ext / "final.json").exists())
        self.assertEqual(self.replay_followup(ext)[0], 0)
        self.assertEqual(self.replay_followup(out)[0], 2)
        self.assertEqual(self.ledger()[-1]["stage"], "second")

    def test_the_plan_starts_from_the_pairs_of_each_cell(self):
        # The second cell had 30 pairs and a control that is narrow but
        # outside the window, so its plan is the floor, 60; the first had
        # 20 and a wide one, so its plan is the cap.
        self.new_control = lambda c, s, pairs, seed: (
            ttg.WIDE if (c, s) == CELL_A and pairs < 40 else
            (1.031, 1.04) if (c, s) == CELL_B and pairs < 60 else ttg.GOOD)
        out, code, text = self.run_followup()
        ext, code, text = self.extend_followup(out)
        self.assertIn('PLAN 2 cells: [["exclude_empty", 100, 120], '
                      '["exclude_missing", 1000, 60]]', text)

    def test_the_second_stage_binds_by_the_seals_and_needs_no_pilot(self):
        # extend_followup passes none: the replaced grid is bound by the
        # seals of the counts, its cells replayed from their archives.
        out, code, _ = self.run_followup()
        self.analyses.clear()
        ext, code, text = self.extend_followup(out)
        self.assertEqual(code, 0, text)
        replaced = {(r["case"], r["size"]) for r in self.analyses
                    if r["seed"] == "s0"}
        self.assertEqual(replaced, {CELL_A, CELL_B})
        self.assertNotIn("TOY two-stage archives", text)

    def test_a_replay_replays_the_replaced_second_stage_in_full(self):
        out, code, _ = self.run_followup()
        ext, code, _ = self.extend_followup(out)
        self.analyses.clear()
        code, text = self.replay_followup(ext)
        self.assertEqual(code, 0, text)
        self.assertEqual(text.count("TOY two-stage archives and decisions"),
                         1)
        self.assertEqual({(r["case"], r["size"]) for r in self.analyses
                          if r["seed"] in ("s0", "s0-ext")},
                         set(self.table.keys()))


class Ledger(Rig):
    """Evidence of a follow-up is kept under the family it names."""

    def test_the_ledger_stamp_and_refs_are_those_of_the_family(self):
        plain = tg.Grid(self.make_followup(ledger=None, family=None))
        own = tg.Grid(self.make_followup(ledger=None))
        repo = self.repo.resolve()
        base = repo / ".agent-files" / "evidence"
        self.assertEqual(plain.ledger_path(repo),
                         base / "toyf" / "attempts.jsonl")
        self.assertEqual(own.ledger_path(repo),
                         base / "toy" / "attempts.jsonl")
        # The stamp and the log of the family's own table keep their names,
        # those of another table of the family carry its name.
        self.assertEqual(own.stamp_path(repo),
                         base / "toy" / "build-stamp-toyf.json")
        self.assertEqual(own.prepare_log_path(repo),
                         base / "toy" / "prepare-toyf.log")
        self.assertEqual(plain.stamp_path(repo),
                         base / "toyf" / "build-stamp.json")
        self.assertEqual(
            tg.Grid(self.make_table(ledger=None)).stamp_path(repo),
            base / "toy" / "build-stamp.json")
        self.assertEqual(
            tg.Grid(self.make_table(ledger=None)).prepare_log_path(repo),
            base / "toy" / "prepare.log")
        self.assertEqual(
            tg.Grid(self.make_table(ledger=None)).ledger_path(repo),
            own.ledger_path(repo))
        own.keep(self.repo, FOLLOW)
        plain.keep(self.repo, FOLLOW)
        self.assertEqual(self.kept[-2:], [("toy", FOLLOW), ("toyf", FOLLOW)])


class Binding(Rig):
    """The replaced grid is bound in full by `predeclare` and `replay` and by
    the seals of the counts by `verify-counts`, `run` and `extend`."""

    def archives(self, folder):
        """Count the archives of a folder that are unpacked."""
        real, seen = tg.bundle.unpack, []

        def unpack(archive, output):
            if folder in Path(archive).parts[-2:-1]:
                seen.append(Path(archive).name)
            return real(archive, output)
        return patch.object(tg.bundle, "unpack", unpack), seen

    def test_a_two_stage_grid_is_replaced_end_to_end(self):
        self.assertEqual(self.load(self.replaced / "inventory.json")[
            "schema"], "toy-extension-v1")
        self.declare()
        self.new_candidate = lambda c, s, pairs, seed: ttg.GOOD
        out, code, text = self.run_followup()
        self.assertEqual(code, 0, text)
        self.assertEqual(self.replay_followup(out)[0], 0)
        self.assertEqual(self.load(out / "inventory.json")["replaces"][
            "grid"], "../replaced")

    def test_a_first_stage_with_a_second_stage_to_come_is_not_replaced(self):
        self.pilot()
        # The first stage remeasures the second cell: its second stage is
        # the grid, not it.
        self.replaced = self.replaced1
        with self.assertRaisesRegex(
                ValueError, "replaced grid is not final.*second stage"):
            self.predeclare()
        self.assertFalse(self.fcounts.exists())

    def test_a_first_stage_with_no_second_stage_to_come_is_replaced(self):
        self.old_control = lambda c, s, pairs, seed: ttg.GOOD
        self.replaced, status, _ = self.first(name="replaced-final")
        self.assertEqual(status, 2)
        self.declare()
        self.assertEqual(self.load(self.fcounts)["pairs_by_cell"],
                         {CELLS[0]: 20, CELLS[1]: 20})
        self.assertEqual(sorted(self.load(self.fcounts)["replaces"][
            "files"]), ["decisions.json", "inventory.json"])

    def test_a_change_to_a_file_of_the_replaced_grid_is_named(self):
        self.declare()
        out, code, _ = self.run_followup()
        commands = self.sealed_commands(out)
        for name in ("inventory.json", "decisions.json",
                     "../replaced-1/inventory.json",
                     "../replaced-1/decisions.json"):
            path = self.replaced / name
            good = path.read_text()
            path.write_text(good.replace("}", " }", 1))
            try:
                for action, argv in commands.items():
                    with self.subTest(name, action=action), \
                            self.assertRaisesRegex(
                                ValueError, "replaced grid changed since "
                                "predeclare: " + name.replace(".", r"\.")):
                        self.fgo(argv)
            finally:
                path.write_text(good)
        self.assertFalse((self.root / "late").exists())

    def test_a_change_to_the_code_of_the_replay_is_named(self):
        self.declare()
        out, code, _ = self.run_followup()
        commands = self.sealed_commands(out)
        real = tg.Grid.replay_code

        def changed(grid):
            return {**real(grid), "summarize.py": dict(
                bytes=1, sha256="0" * 64)}
        with patch.object(tg.Grid, "replay_code", changed):
            for action, argv in commands.items():
                with self.subTest(action), self.assertRaisesRegex(
                        ValueError, r"code changed since predeclare: "
                        r"summarize\.py; run predeclare again"):
                    self.fgo(argv)
        self.assertFalse((self.root / "late").exists())

    def test_the_counts_file_of_the_replaced_table_is_code_of_the_replay(
            self):
        self.declare()
        good = self.counts.read_text()
        self.counts.write_text(good + " ")
        try:
            with self.assertRaisesRegex(
                    ValueError, "code changed since predeclare: " +
                    self.counts.name.replace(".", r"\.")):
                self.fgo(self.sealed_commands(None)["verify-counts"])
        finally:
            self.counts.write_text(good)

    def test_the_headers_of_the_replaced_grid_are_checked_by_the_seals(self):
        self.declare()
        out, code, _ = self.run_followup()
        seen = []
        for name in ("check_header", "check_sources", "check_commit",
                     "check_checkout"):
            real = getattr(self.grid, name)

            def counted(inventory, *rest, real=real, name=name):
                seen.append((name, inventory["schema"]))
                return real(inventory, *rest)
            setattr(self.grid, name, counted)
        self.fgo(self.sealed_commands(out)["verify-counts"])
        self.assertEqual(sorted(seen), sorted(
            (n, s) for n in ("check_header", "check_sources", "check_commit",
                             "check_checkout")
            for s in ("toy-experiment-v1", "toy-extension-v1")))
        self.grid.check_header = lambda inventory: (_ for _ in ()).throw(
            ValueError("header refused"))
        for action, argv in self.sealed_commands(out).items():
            if action == "extend":
                continue
            with self.subTest(action), self.assertRaisesRegex(
                    ValueError, "header refused"):
                self.fgo(argv)
        self.assertFalse((self.root / "late").exists())

    def test_the_seals_are_those_of_the_counts_whatever_the_grid(self):
        self.declare()
        out, code, _ = self.run_followup()
        counts = self.load(self.fcounts)
        for label, change in (
                ("a file less", lambda r: r["files"].pop(
                    "../replaced-1/decisions.json")),
                ("a file more", lambda r: r["files"].update(
                    {"matrix.json": dict(bytes=1, sha256="0" * 64)})),
                ("other open cells", lambda r: r.update(open=[CELLS[0]])),
                ("no record", lambda r: r.clear())):
            with self.subTest(label):
                changed = json.loads(json.dumps(counts))
                change(changed["replaces"])
                self.fcounts.write_text(json.dumps(changed))
                with self.assertRaisesRegex(ValueError, "changed since "
                                            "predeclare|open cells differ|"
                                            "record no replaced grid"):
                    self.fgo(self.sealed_commands(out)["verify-counts"])
        self.fcounts.write_text(json.dumps(counts))

    def test_only_the_cells_of_the_follow_up_are_replayed_by_a_seal_binding(
            self):
        self.declare()
        patcher, seen = self.archives("replaced-1")
        self.analyses.clear()
        with patcher:
            code, text = self.fgo(self.sealed_commands(None)["verify-counts"])
        self.assertEqual(code, 0, text)
        self.assertEqual(len(seen), 2)
        self.assertEqual({(r["case"], r["size"]) for r in self.analyses
                          if r["seed"] == "s0"}, {CELL_A, CELL_B})
        self.assertNotIn("TOY two-stage archives", text)
        # The full replay (predeclare, replay) goes through every cell of
        # both stages.
        patcher, seen = self.archives("replaced-1")
        with patcher:
            self.fcounts.unlink()
            self.assertEqual(self.predeclare()[0], 0)
        self.assertEqual(len(seen), len(self.table.keys()))

    def test_a_changed_archive_of_a_follow_up_cell_is_found_at_once(self):
        self.declare()
        real = tg.bundle.unpack

        def unpack(archive, output):
            if "replaced-1" in Path(archive).parts[-2:-1]:
                raise ValueError("changed archive")
            return real(archive, output)
        with patch.object(tg.bundle, "unpack", unpack):
            for action, argv in self.sealed_commands(None).items():
                if action == "extend":
                    continue
                with self.subTest(action), self.assertRaisesRegex(
                        ValueError, "changed archive"):
                    self.fgo(argv)

    def test_a_helper_before_the_grid_is_bound_is_a_refusal(self):
        fresh = tg.Grid(self.make_followup())
        inventory = dict(layout_seed="f0", iterations_seal={},
                         replaces={}, candidate=FOLLOW, sources=None)
        for label, call in (
                ("bound", lambda: fresh.bound()),
                ("replaces_record", lambda: fresh.replaces_record(
                    self.root, inventory)),
                ("followup_pairs", lambda: fresh.followup_pairs()),
                ("replaced_counts", lambda: fresh.replaced_counts(
                    self.fpilot)),
                ("check_replaced", lambda: fresh.check_replaced(
                    inventory, self.root, self.repo))):
            with self.subTest(label), self.assertRaisesRegex(
                    ValueError, "has not bound the grid it replaces"):
                call()
        with self.assertRaisesRegex(ValueError, "TOY replaces no grid"):
            self.grid.bound()

    def test_the_replaced_grid_is_replayed_by_its_engine_with_its_hooks(self):
        # The engine the table names is the one that replays: a hook of it
        # is used, not the defaults of a bare table.
        class Marked(tg.Grid):
            replays = 0

            def replay(self, args):
                Marked.replays += 1
                return super().replay(args)
        engine = Marked(self.table)
        self.fgrid = tg.Grid(self.make_followup(
            replaces=tg.Replaces(engine)))
        self.pilot()
        self.assertEqual(self.predeclare()[0], 0)
        self.assertEqual(Marked.replays, 1)
        self.assertIs(self.fgrid.t.replaces.engine, engine)

    def test_the_ledger_option_reaches_the_replay_of_predeclare(self):
        self.pilot()
        elsewhere = self.root / "elsewhere.jsonl"
        elsewhere.write_text(self.attempts.read_text())
        self.attempts.rename(self.root / "moved.jsonl")
        with self.assertRaisesRegex(ValueError, "no attempts ledger"):
            self.predeclare()
        self.assertEqual(self.predeclare("--ledger", str(elsewhere))[0], 0)
        self.assertEqual(self.fgo(
            ["verify-counts", "--grid", str(self.fpilot), "--repo",
             str(self.repo), "--ledger", str(elsewhere), *self.over()])[0],
            0)


class SameLedger(Rig):
    """A follow-up appends to the ledger that holds the openings of the
    replaced grid, and starts no chain of its own."""

    def test_a_missing_ledger_is_refused_and_not_created(self):
        self.declare()
        out, code, _ = self.run_followup("good")
        moved = self.attempts.with_name("moved.jsonl")
        self.attempts.rename(moved)
        for argv in (self.sealed_commands(None)["run"],
                     self.sealed_commands(out)["extend"]):
            with self.assertRaisesRegex(
                    ValueError, "no attempts ledger at .*attempts.*: a "
                    "follow-up appends to the ledger that holds the "
                    "openings of the replaced grid"):
                self.fgo(argv)
        self.assertFalse(self.attempts.exists())
        self.assertFalse((self.root / "late").exists())
        self.assertFalse((self.root / "late-ext").exists())

    def test_a_ledger_without_the_replaced_openings_is_refused(self):
        self.declare()
        out, code, _ = self.run_followup("good")
        before = self.attempts.read_text()
        self.attempts.unlink()
        tg.ledger_append(
            self.attempts, event="open", stage="first", attempt="f" * 32,
            candidate=FOLLOW, table="toyf", counts_file="x.json",
            counts=dict(bytes=1, sha256="0" * 64), seed="f0",
            output="/o", checkout="/c", only=None)
        for argv in (self.sealed_commands(None)["run"],
                     self.sealed_commands(out)["extend"]):
            with self.assertRaisesRegex(
                    ValueError, "attempts ledger .* lacks the first-stage "
                    "opening of attempt [0-9a-f]+ of the replaced grid"):
                self.fgo(argv)
        self.assertFalse((self.root / "late").exists())
        self.attempts.write_text(before)

    def test_the_ledger_with_the_openings_of_both_stages_is_accepted(self):
        self.declare()
        out, code, _ = self.run_followup("good")
        self.assertIn(code, (0, 2))
        state = tg.Ledger(self.attempts)
        self.assertEqual(len([r for r in state.records
                              if r.get("table") == "toy"
                              and r["event"] == "open"]), 2)

    def test_the_second_stage_of_the_replaced_grid_is_needed_too(self):
        self.declare()
        lines = self.attempts.read_text().splitlines()
        keep = [x for x in lines if '"stage": "second"' not in x or
                '"table": "toyf"' in x]
        self.attempts.write_text("\n".join(keep) + "\n")
        with self.assertRaisesRegex(
                ValueError, "lacks the second-stage opening"):
            self.fgo(self.sealed_commands(None)["run"])


class TableOfLine(Rig):
    """The lines of the ledger name their table, and the lines written
    before they did belong to the table of the family."""

    def legacy(self, path, attempt, candidate):
        """A line as the engine wrote it before the field existed."""
        tg.ledger_append(
            path, event="open", stage="first", attempt=attempt,
            candidate=candidate, counts_file="toy_iterations.json",
            counts=dict(bytes=1, sha256="0" * 64), seed="s0",
            output="/out", checkout="/c", only=None)

    def inventory_of(self, attempt, candidate, seed):
        return dict(attempt=attempt, candidate=candidate,
                    counts_file="x.json", iterations_seal=dict(
                        bytes=1, sha256="1" * 64), layout_seed=seed)

    def test_new_lines_name_their_table_and_old_ones_are_the_familys(self):
        path = self.root / "mixed.jsonl"
        self.legacy(path, "old1", ttg.CANDIDATE)
        self.legacy(path, "old2", FOLLOW)
        before = path.read_text()
        self.grid.record_attempt(
            path, "open", "first", self.inventory_of("t1", FOLLOW, "s0"),
            "/o", self.repo)
        self.fgrid.record_attempt(
            path, "open", "first", self.inventory_of("f1", FOLLOW, "f0"),
            "/o", self.repo)
        self.fgrid.record_attempt(
            path, "close", "first", self.inventory_of("f1", FOLLOW, "f0"),
            "/o", self.repo, status="pass")
        # The lines already there are as they were, and the chain holds.
        self.assertTrue(path.read_text().startswith(before))
        state = tg.Ledger(path)
        self.assertEqual(len(state.records), 5)
        self.assertEqual([r.get("table") for r in state.records],
                         [None, None, "toy", "toyf", "toyf"])
        # TASK30's counts are its own lines (old ones included), the
        # follow-up's its own.
        self.assertEqual(self.grid.attempt_counts(state, FOLLOW), (3, 2))
        self.assertEqual(self.fgrid.attempt_counts(state, FOLLOW), (1, 1))
        self.assertEqual(self.fgrid.attempt_counts(state, ttg.CANDIDATE),
                         (1, 0))

    def test_an_attempt_report_and_close_count_their_own_table(self):
        path = self.root / "mixed.jsonl"
        self.legacy(path, "old1", ttg.CANDIDATE)
        self.fgrid.record_attempt(
            path, "open", "first", self.inventory_of("f1", FOLLOW, "f0"),
            "/o", self.repo)
        state = tg.Ledger(path)
        for engine, label, text in (
                (self.grid, "TOY", "1 in the ledger, 0 of this candidate"),
                (self.fgrid, "TOYF", "1 in the ledger, 1 of this candidate")):
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                engine.report_attempts(
                    state, self.inventory_of(
                        "x", FOLLOW, None), "first")
            self.assertIn("ATTEMPTS of %s: %s" % (label, text),
                          out.getvalue())
            self.assertIn("(1 records of %s, 2 in the ledger, chain intact)"
                          % label, out.getvalue())
            self.assertEqual(out.getvalue().count("\nATTEMPT ") +
                             out.getvalue().startswith("ATTEMPT "), 1)

    def test_a_follow_up_run_leaves_the_replaced_grids_counts_alone(self):
        self.declare()
        before = self.grid.attempt_counts(
            tg.Ledger(self.attempts), ttg.CANDIDATE)
        self.run_followup()
        state = tg.Ledger(self.attempts)
        self.assertEqual(self.grid.attempt_counts(state, ttg.CANDIDATE),
                         before)
        self.assertEqual(self.fgrid.attempt_counts(state, FOLLOW), (1, 1))
        self.assertEqual({r["table"] for r in state.records},
                         {"toy", "toyf"})

    def test_an_opening_of_another_table_is_not_this_grids(self):
        self.declare()
        out, code, _ = self.run_followup()
        inventory = self.load(out / "inventory.json")
        self.assertIsNotNone(self.fgrid.check_attempt(
            argparse.Namespace(repo=self.repo, ledger=None), inventory,
            "first"))
        # The toy table has no opening of the follow-up's attempt.
        with self.assertRaisesRegex(ValueError, "no opening of this grid"):
            self.grid.check_attempt(
                argparse.Namespace(repo=self.repo, ledger=None), inventory,
                "first")


class Prepare(ttg.ChainRig):
    """`prepare` of a table of a family keeps its own stamp and log, and
    leaves those of the table that names the family."""

    def test_a_follow_up_prepare_keeps_the_stamp_and_log_of_the_family(self):
        self.commit_counts()
        stamp = self.stamp()
        log = stamp.with_name("prepare.log")
        before = (stamp.read_text(), log.read_text())
        fdriver = self.root / "toyf_grid.py"
        fdriver.write_text("# the toy follow-up driver\n")
        table = tg.Table(
            "toyf", "TOYF", CASES, fdriver, self.root / "toyf.json",
            cells=CELLS, family="toy", replaces=tg.Replaces(self.grid),
            seconds=0.3, seconds_by_case={CASES[0]: ttg.LONG},
            fixed_seconds=True, schedule="warmup", pairs=2 * self.pairs,
            samples=self.samples, seed="f0", baseline=self.base,
            tree="src", sources=ttg.SOURCES, sealed=ttg.SEALED,
            home=self.sealed_dir, root=self.root)
        grid = tg.Grid(table)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertEqual(
                grid.execute(["prepare", "--repo", str(self.repo)]), 0)
        # Its own stamp and log are there; the family's are as they were.
        mine = grid.stamp_path(self.repo)
        self.assertEqual(mine.name, "build-stamp-toyf.json")
        self.assertTrue(mine.is_file())
        self.assertTrue(grid.prepare_log_path(self.repo).is_file())
        self.assertEqual((stamp.read_text(), log.read_text()), before)
        # And the other way: the table of the family leaves the follow-up's.
        own = mine.read_text()
        with contextlib.redirect_stdout(out):
            self.assertEqual(
                self.grid.execute(["prepare", "--repo", str(self.repo)]), 0)
        self.assertEqual(mine.read_text(), own)
        self.assertNotEqual(stamp.read_text(), before[0])


tearDownModule = ttg.tearDownModule


if __name__ == "__main__":
    unittest.main()
