#!/usr/bin/env python3
"""A follow-up table of the shared timing grid: the cells it takes over from a
grid that left them inconclusive, their pairs, the replaced grid's replay, the
refusals, `final.json`, its own second stage and the evidence family.

The rig is that of test_timing_grid.py: a toy table whose first stage is the
replaced grid, a toy follow-up of two of its cells, and the same stand-ins.
"""
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
# interval GOOD (half log-width 0.01), that of the second 0.0253.
CELL_A, CELL_B = (CASES[0], 100), (CASES[1], 1000)
CELLS = tuple("%s-%d" % k for k in (CELL_A, CELL_B))
MID = (0.975, 1.025)


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
            cells=CELLS, family="toy", replaces=tg.Replaces(self.OLD),
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
            self.follow(replaces=tg.Replaces(small))

    def test_a_replaces_is_a_replaces(self):
        with self.assertRaisesRegex(ValueError, "malformed replaces"):
            self.follow(replaces=self.OLD)
        with self.assertRaisesRegex(ValueError, "unknown replacement"):
            tg.Replaces(self.OLD, "failed")

    def test_the_seed_of_the_follow_up_may_end_in_ext_of_its_own(self):
        self.assertEqual(self.follow(seed="f0-x").seed, "f0-x")


class Rig(ttg.Rig):
    """The replaced grid (toy, 10 pairs, 12 cells, two of them inconclusive)
    and a follow-up table (toyf, 20 pairs at the least) of those two."""
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
        self.replaced, status, _ = self.first(name="replaced")
        self.assertEqual(status, 2)
        self.ftable = self.make_followup()
        self.fgrid = tg.Grid(self.ftable)
        self.runs.clear()
        self.launched.clear()

    def mid_control(self, case, size, pairs, seed):
        return MID if (case, size) == CELL_B else ttg.GOOD

    def wide_when_open(self, case, size, pairs, seed):
        return ttg.WIDE if (case, size) in self.OPEN else ttg.GOOD

    def make_followup(self, **kw):
        options = dict(
            cells=CELLS, family="toy", replaces=tg.Replaces(self.table),
            seconds=0.3, seconds_by_case={CASES[0]: ttg.LONG},
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
            "--replaces-pilot", str(self.pilot_dir),
            "--authorize-measurements", *extra])
        return out, code, text

    def replay_followup(self, out, *extra):
        return self.fgo(["replay", "--output", str(out), "--repo",
                         str(self.repo), "--pilot", str(self.fpilot),
                         "--replaces-pilot", str(self.pilot_dir), *extra])

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
        self.assertEqual(counts["replaces"], dict(
            inventory=a.seal(self.replaced / "inventory.json"),
            decisions=a.seal(self.replaced / "decisions.json")))
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
        self.replaced, status, _ = self.first(name="replaced-2")
        self.assertEqual(status, 2)
        code, text = self.stage(self.replaced)
        self.assertIn("PLAN", text)
        self.replaced = self.root / "stage2"
        self.declare()
        self.assertEqual(self.load(self.fcounts)["pairs_by_cell"],
                         {CELLS[0]: 120, CELLS[1]: 20})

    def stage(self, grid):
        return self.go(self.argv(
            "extend", self.root / "stage2", "--grid", str(grid),
            "--authorize-measurements"))

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

    def declare_followup_again(self):
        self.fcounts.unlink()
        self.assertEqual(self.predeclare()[0], 0)

    def test_counts_of_another_replaced_grid_are_refused(self):
        self.declare()
        other, status, _ = self.first(name="replaced-again")
        self.assertEqual(status, 2)
        self.replaced = other
        with self.assertRaisesRegex(ValueError, "pairs or the replaced grid"):
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
        self.replaced, status, _ = self.first(name="replaced-one")
        self.assertEqual(status, 2)
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
        self.assertEqual(inventory["replaces"], dict(
            grid="../replaced", inventory=a.seal(self.replaced /
                                              "inventory.json"),
            decisions=a.seal(self.replaced / "decisions.json")))
        self.assertIn(("toy", FOLLOW), self.kept)
        records = self.ledger()
        self.assertEqual({r["output"] for r in records[-2:]},
                         {str(out)})
        self.assertEqual(records[-2]["counts_file"], "toyf_iterations.json")
        self.assertEqual(len({r["attempt"] for r in self.ledger()}), 2)

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

    def test_final_json_is_the_replaced_decision_with_the_cells_replaced(
            self):
        self.settled()
        out, code, text = self.run_followup()
        self.assertEqual(code, 0, text)
        final = self.load(out / "final.json")
        old = self.load(self.replaced / "decisions.json")
        self.assertEqual((old["status"], final["status"]),
                         ("inconclusive", "pass"))
        self.assertEqual(final["schema"], "toy-grid-v1")
        self.assertEqual(len(final["workloads"]), 12)
        rows = lambda d: {(r["case"], r["size"]): r for r in d["workloads"]}
        for key, row in rows(final).items():
            same = key not in (CELL_A, CELL_B)
            self.assertEqual(row == rows(old)[key], same, key)
        first = self.load(self.replaced / "inventory.json")
        self.assertEqual(final["replaced"], dict(
            cells=list(CELLS), seed="s0", counts=first["iterations_seal"],
            candidates=dict(replaced=ttg.CANDIDATE, followup=FOLLOW),
            rule="the cells the replaced grid left inconclusive, "
            "measured again"))
        self.assertIn("TOY with the follow-up grid: pass (pass 12", text)
        code, text = self.replay_followup(out)
        self.assertEqual(code, 0, text)

    def test_a_follow_up_fail_is_a_fail_of_the_final_decision(self):
        self.settled(ci_b=(1.04, 1.08))
        out, code, text = self.run_followup()
        self.assertEqual(code, 1, text)
        self.assertEqual(self.load(out / "final.json")["status"], "fail")
        self.assertEqual(self.replay_followup(out)[0], 1)

    def test_a_final_decision_that_was_changed_does_not_replay(self):
        self.settled()
        out, code, _ = self.run_followup()
        good = (out / "final.json").read_text()
        final = json.loads(good)
        for label, change in (
                ("status", lambda f: f.update(status="fail")),
                ("a cell", lambda f: f["workloads"][0].update(exit=1)),
                ("the replaced block", lambda f: f["replaced"].update(
                    seed="s1")),
                ("a candidate", lambda f: f["replaced"]["candidates"]
                 .update(followup=ttg.CANDIDATE))):
            with self.subTest(label):
                changed = json.loads(good)
                change(changed)
                (out / "final.json").write_text(json.dumps(changed))
                with self.assertRaisesRegex(ValueError, "final decisions"):
                    self.replay_followup(out)
        (out / "final.json").unlink()
        with self.assertRaisesRegex(ValueError, "final decisions"):
            self.replay_followup(out)
        (out / "final.json").write_text(good)
        self.assertEqual(self.replay_followup(out)[0], 0)
        self.assertEqual(final["status"], "pass")

    def test_the_replay_replays_the_replaced_grid_too(self):
        self.settled()
        out, code, _ = self.run_followup()
        code, text = self.replay_followup(out)
        self.assertEqual(code, 0)
        self.assertEqual(text.count("TOY archives and decisions replayed"),
                         1)
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
        self.assertFalse((out / "final.json").exists())
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
        with self.assertRaisesRegex(ValueError, "needs --replaces-pilot"):
            self.fgo(["run", "--output", str(self.root / "x"), "--repo",
                      str(self.repo), "--pilot", str(self.fpilot),
                      "--candidate", FOLLOW, "--authorize-measurements",
                      "--replaces", str(self.replaced)])
        self.assertEqual(self.runs, [])

    def test_a_table_that_replaces_nothing_takes_no_grid(self):
        for argv in (
                ["run", "--output", str(self.root / "x"), "--repo",
                 str(self.repo), "--pilot", str(self.pilot_dir),
                 "--candidate", CANDIDATE_OTHER,
                 "--authorize-measurements", "--replaces",
                 str(self.replaced)],
                ["extend", "--grid", str(self.replaced), "--output",
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
        out, status, _ = self.first(name="replaced-other")
        self.assertEqual(status, 2)
        self.replaced = out

    def test_other_cells_than_the_open_ones_are_refused(self):
        self.other_replaced({CELL_A, (CASES[1], 0)})
        self.refused("follow-up cells differ from the open cells")

    def test_fewer_cells_than_the_open_ones_are_refused(self):
        self.other_replaced({CELL_A})
        self.refused("follow-up cells differ from the open cells")

    def test_more_cells_than_the_open_ones_are_refused(self):
        self.other_replaced({CELL_A, CELL_B, (CASES[1], 0)})
        self.refused("follow-up cells differ from the open cells")

    def test_sources_other_than_the_replaced_grids_are_refused(self):
        # The pin of the follow-up accepts a blob of a file that the replaced
        # grid had at another (it, too, pinned).
        pins = {"src/one.sml": dict(blob="f" * 40, reason="A change.")}
        self.refused_with_pins(pins)

    def refused_with_pins(self, pins):
        self.differ = {"src/one.sml"}
        self.table.pinned = pins
        old, status, _ = self.first(name="replaced-pinned")
        self.assertEqual(status, 2)
        self.replaced = old
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
        old, status, _ = self.first(name="replaced-pinned")
        self.replaced = old
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
        table = self.make_followup(home=self.repo / "area")
        self.fgrid = tg.Grid(table)
        self.assertEqual(self.fgrid.sealed_paths(self.repo), {
            "area/one.txt", "area/two.txt"})
        self.between = [["M", "area/one.txt"]]
        self.fgrid.replaced = dict(first=dict(
            candidate=ttg.CANDIDATE, layout_seed="s0", sources=None,
            baseline=a.BASE))
        inventory = dict(
            replaces=1, layout_seed="f0", candidate=FOLLOW,
            sources=None)
        with patch.object(self.fgrid, "replaces_record", lambda root: 1):
            self.fgrid.check_replaced(inventory, self.root, self.repo)
            self.between = [["M", "area/three.txt"]]
            with self.assertRaisesRegex(ValueError, "area/three.txt"):
                self.fgrid.check_replaced(inventory, self.root, self.repo)

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
        self.assertFalse((out / "final.json").exists())
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
        final = self.load(ext / "final.json")
        self.assertEqual(final["status"], "pass")
        self.assertEqual(final["replaced"]["cells"], list(CELLS))
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

    def test_a_first_stage_with_a_second_stage_to_come_has_no_final(self):
        out, code, _ = self.run_followup()
        self.assertFalse((out / "final.json").exists())
        (out / "final.json").write_text("{}")
        with self.assertRaisesRegex(ValueError,
                                    "final.json before the second stage"):
            self.replay_followup(out)

    def test_the_second_stage_final_decision_is_checked_on_replay(self):
        out, code, _ = self.run_followup()
        ext, code, _ = self.extend_followup(out)
        final = self.load(ext / "final.json")
        final["workloads"][0]["exit"] = 1
        (ext / "final.json").write_text(json.dumps(final))
        with self.assertRaisesRegex(ValueError, "final decisions"):
            self.replay_followup(ext)

    def test_the_second_stage_needs_the_replaced_grids_pilot(self):
        out, code, _ = self.run_followup()
        with self.assertRaisesRegex(ValueError, "needs --replaces-pilot"):
            self.fgo(["extend", "--grid", str(out), "--output",
                      str(self.root / "e"), "--repo", str(self.repo),
                      "--pilot", str(self.fpilot),
                      "--authorize-measurements"])


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
        self.assertEqual(own.stamp_path(repo),
                         base / "toy" / "build-stamp.json")
        self.assertEqual(
            tg.Grid(self.make_table(ledger=None)).ledger_path(repo),
            own.ledger_path(repo))
        own.keep(self.repo, FOLLOW)
        plain.keep(self.repo, FOLLOW)
        self.assertEqual(self.kept[-2:], [("toy", FOLLOW), ("toyf", FOLLOW)])


tearDownModule = ttg.tearDownModule


if __name__ == "__main__":
    unittest.main()
