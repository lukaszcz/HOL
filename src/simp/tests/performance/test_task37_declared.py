"""task37_declared.py and task37_declared.json: the TASK37 declaration of
the final candidate, its placeholder, and how it is observed and filled.
No HOL, no build, no measurement."""
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import task32_downstream as d
import task33_offline as offline
import task33_rules as rules
import task37_cases as cases37
import task37_declared as t

KINDS = ["state-empty", "first-use"]
HEAP = "bin/hol.state"
NAMES = ["simpLib", "Traverse", "Travrules", "Opening", "boolSimps",
         "pureSimps"]


def proc(total, d=100, rows=None, ok=True):
    rows = rows or {n: 10 for n in NAMES}
    return dict(anchored=dict(total=[total] * 3, d=[d] * 3, repeat_ok=ok,
                              rows={n: [v] * 3 for n, v in rows.items()}))


def groups(base=1000, cand=1010, n=2, rows_c=None, kinds=KINDS):
    return {k: dict(base=[proc(base) for _ in range(n)],
                    cand=[proc(cand, 105, rows_c) for _ in range(n)])
            for k in kinds}


def load():
    return offline.load_declared(t.DECLARED)


class TheDeclaration(unittest.TestCase):
    def test_only_the_s2_placeholder_is_open(self):
        d = load()
        self.assertEqual(offline.count_problems(d), [])
        bad = offline.shape_problems(d)
        self.assertTrue(bad)
        self.assertTrue(all(x.startswith("s2.total_delta[0]") for x in bad),
                        bad)
        self.assertIn("pending", bad[0])

    def test_the_counts_are_the_final_candidates(self):
        counts = load()["log_counts"]
        self.assertEqual(counts["split-lifecycle"], 2217)
        self.assertEqual(counts["fresh-load-regressions"], 147)
        self.assertEqual(counts["split-persistence"], 170)
        old = offline.load_declared()["log_counts"]
        self.assertEqual(sorted(counts), sorted(old))

    def test_task33s_declaration_is_untouched_by_the_selection(self):
        before = offline.DECLARED
        previous = offline.use_declared(t.DECLARED)
        try:
            self.assertEqual(previous, before)
            self.assertEqual(offline.DECLARED, t.DECLARED)
            self.assertEqual(offline.load_declared()["cand"],
                             load()["cand"])
        finally:
            offline.use_declared(previous)
        self.assertEqual(offline.DECLARED, before)
        self.assertEqual(offline.load_declared()["cand"],
                         "e436752631f54a563679bd184a64c3d4ed249c23")

    def test_a_placeholder_is_never_a_decision_input(self):
        with self.assertRaises(rules.Inadmissible):
            rules.total_deltas(load())

    def test_the_log_counts_are_what_judge_log_reads(self):
        text = "".join("t%d ... OK\n" % i for i in range(147))
        passed, reasons, counts = offline.judge_log(
            "src/simp/src/.hol/logs/fresh-load-regressions", text +
            "".join("OBS result=pass\n" for _ in range(1)), load())
        self.assertEqual(counts["ok_lines"], 147)
        self.assertFalse([r for r in reasons if "no reviewed" in r])

    def test_the_declared_blobs_are_those_of_the_pins(self):
        repo = HERE.parents[3]
        d = load()
        try:
            def blob(rev, p):
                return subprocess.run(
                    ["git", "-C", str(repo), "rev-parse", rev + ":" + p],
                    stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                    stdin=subprocess.DEVNULL, check=True
                ).stdout.decode().strip()
            for e in d["l2"] + d["allowlist"]:
                self.assertEqual(blob(d["cand"], e["path"]), e["cand_blob"])
                self.assertEqual(blob(d["base"], e["path"]), e["base_blob"])
        except (subprocess.CalledProcessError, OSError):
            self.skipTest("the pinned commits are not in this repository")


class Observation(unittest.TestCase):
    def test_a_constant_growth_is_the_value(self):
        obs = t.observation(groups(rows_c={n: 9 for n in NAMES}), HEAP,
                            KINDS)
        self.assertEqual(obs["value"], 10)
        self.assertEqual(obs["observed"]["base"], 1000)
        self.assertEqual(obs["observed"]["processes_per_side_per_kind"], 2)
        self.assertEqual(obs["observed"]["exclusive"]["simpLib"], [10, 9])

    def test_a_value_that_varies_is_refused(self):
        g = groups()
        g["first-use"]["cand"][1] = proc(1011, 105)
        with self.assertRaisesRegex(t.Refusal, "differs"):
            t.observation(g, HEAP, KINDS)

    def test_a_growing_exclusive_part_is_a_finding(self):
        rows = {n: 10 for n in NAMES}
        rows["Traverse"] = 11
        with self.assertRaisesRegex(t.Refusal, "Traverse"):
            t.observation(groups(rows_c=rows), HEAP, KINDS)

    def test_no_growth_is_refused(self):
        with self.assertRaisesRegex(t.Refusal, "does not grow"):
            t.observation(groups(cand=1000), HEAP, KINDS)
        with self.assertRaisesRegex(t.Refusal, "does not grow"):
            t.observation(groups(cand=990), HEAP, KINDS)

    def test_unrepeatable_or_missing_totals_are_refused(self):
        g = groups()
        g["state-empty"]["base"][0] = proc(1000, ok=False)
        with self.assertRaisesRegex(t.Refusal, "repeats"):
            t.observation(g, HEAP, KINDS)
        g = groups()
        g["state-empty"]["base"][0]["anchored"]["total"] = None
        with self.assertRaisesRegex(t.Refusal, "not computed"):
            t.observation(g, HEAP, KINDS)

    def test_the_kinds_must_be_exactly_the_entrys(self):
        with self.assertRaisesRegex(t.Refusal, "kinds"):
            t.observation(groups(kinds=KINDS[:1]), HEAP, KINDS)

    def test_sides_must_have_the_same_number_of_processes(self):
        g = groups()
        g["state-empty"]["cand"].pop()
        with self.assertRaisesRegex(t.Refusal, "number"):
            t.observation(g, HEAP, KINDS)


def observed():
    rows = {n: 9 for n in NAMES}
    rows["simpLib"], rows["Traverse"] = 9, 9
    # D must fit the structure rule: the total lies between the largest
    # and the sum of the exclusive parts (checked at the record level)
    return t.observation(groups(rows_c=rows), HEAP, KINDS, pins())


def pins(cand="a" * 40):
    return dict(base=load()["base"], cand=cand,
                manifest=dict(bytes=1, sha256="0" * 64))


class Fill(unittest.TestCase):
    def raw(self):
        return json.loads(t.DECLARED.read_text())

    def test_the_filled_declaration_is_valid_and_binds_the_gates(self):
        new = t.fill(self.raw(), observed())
        # the declared candidate is the named constant, not the observation's
        self.assertEqual(new["cand"], cases37.COMPILED_REF)
        self.assertEqual(new["cand"], self.raw()["cand"])
        entry = new["s2"]["total_delta"][0]
        self.assertNotIn("pending", entry)
        self.assertEqual(entry["value"], 10)
        self.assertEqual(t.problems(offline.join_text(new)), [])
        self.assertEqual(rules.total_deltas(offline.join_text(new)),
                         [dict(heap=HEAP, kinds=KINDS, value=10)])

    def test_filling_twice_or_with_other_kinds_is_refused(self):
        new = t.fill(self.raw(), observed())
        with self.assertRaisesRegex(t.Refusal, "placeholder"):
            t.fill(new, observed())
        obs = dict(observed(), kinds=["state-empty"])
        with self.assertRaisesRegex(t.Refusal, "kinds"):
            t.fill(self.raw(), obs)

    def test_a_bad_pin_or_observation_is_refused(self):
        with self.assertRaises(ValueError):  # not a full pin
            t.fill(self.raw(), dict(observed(), cand="7e202dfbaa"))
        with self.assertRaisesRegex(t.Refusal, "base"):
            t.fill(self.raw(), dict(observed(), base="b" * 40))
        with self.assertRaisesRegex(t.Refusal, "base"):
            t.fill(self.raw(), {k: v for k, v in observed().items()
                                if k != "base"})
        with self.assertRaisesRegex(t.Refusal, "not an S2"):
            t.fill(self.raw(), dict(observed(), schema="x"))

    def test_the_cli_checks_fills_and_refuses(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            path = tmp / "declared.json"
            path.write_text(t.DECLARED.read_text())
            self.assertEqual(t.main(["check", "--declared", str(path)]), 0)
            self.assertEqual(t.main(["check", "--final", "--declared",
                                     str(path)]), 1)
            obs = tmp / "obs.json"
            obs.write_text(json.dumps(observed()))
            self.assertEqual(t.main(["fill", "--declared", str(path),
                                     "--observation", str(obs)]), 0)
            self.assertEqual(t.main(["check", "--final", "--declared",
                                     str(path)]), 0)
            self.assertEqual(t.main(["fill", "--declared", str(path),
                                     "--observation", str(obs)]), 3)
            self.assertEqual(t.main(["check", "--declared",
                                     str(tmp / "none.json")]), 3)


class ObserveFolders(unittest.TestCase):
    """`observe_folders` over stage folders whose replay is stubbed: the
    stages must share base, candidate and manifest, which are recorded."""
    def folders(self, tmp, reports):
        out = []
        for i, report in enumerate(reports):
            folder = Path(tmp) / ("f%d" % i)
            folder.mkdir()
            (folder / "downstream.json").write_text(json.dumps(report))
            out.append(folder)
        return out

    def report(self, cand="a" * 40, manifest=None):
        return dict(base=load()["base"], cand=cand, runs=[],
                    manifest=manifest or dict(bytes=1, sha256="0" * 64),
                    units={"registry-" + k: dict(heap=HEAP)
                           for k in KINDS})

    def observe(self, reports):
        import task33_storage as storage
        grouped = {"registry-" + k: sides for k, sides in groups(
            rows_c={n: 9 for n in NAMES}, n=1).items()}
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(storage, "replay_one"), \
                mock.patch.object(storage, "check_plan",
                                  return_value={}), \
                mock.patch.object(storage, "check_redraws",
                                  return_value=[]), \
                mock.patch.object(storage, "grouped",
                                  return_value=grouped):
            return t.observe_folders(self.folders(tmp, reports), None,
                                     load())

    def test_one_gate_gives_an_observation_with_its_pins(self):
        before = d.ACTIVE.name
        obs = self.observe([self.report(), self.report()])
        self.assertEqual(d.ACTIVE.name, before)  # the table is restored
        self.assertEqual(obs["value"], 10)
        self.assertEqual((obs["base"], obs["cand"]),
                         (load()["base"], "a" * 40))
        self.assertEqual(obs["manifest"], pins()["manifest"])
        new = t.fill(json.loads(t.DECLARED.read_text()), obs)
        self.assertEqual(new["cand"], cases37.COMPILED_REF)

    def test_the_stages_are_observed_under_the_task37_table(self):
        import task33_storage as storage
        seen = []
        real = t.observe_stages

        def spy(*args):
            seen.append((d.ACTIVE.name, storage.ACTIVE_STORAGE,
                         storage.LEDGER_TABLE))
            return real(*args)
        before = (d.ACTIVE.name, storage.ACTIVE_STORAGE)
        with mock.patch.object(t, "observe_stages", spy):
            self.observe([self.report()])
        self.assertEqual(seen, [("task37-t33", "task37-t33",
                                 "task37-t33-storage")])
        self.assertEqual((d.ACTIVE.name, storage.ACTIVE_STORAGE), before)

    def test_stages_of_different_candidates_or_manifests_are_refused(self):
        with self.assertRaisesRegex(t.Refusal, "one base, one candidate"):
            self.observe([self.report(), self.report("b" * 40)])
        with self.assertRaisesRegex(t.Refusal, "one base, one candidate"):
            self.observe([self.report(), self.report(
                manifest=dict(bytes=2, sha256="1" * 64))])


if __name__ == "__main__":
    unittest.main()
