#!/usr/bin/env python3
"""TASK37 in the allocation matrix: the pair count of a task, the tasks
`task37-matrix` and `task37-client`, and the refusals around them.

Synthetic receipts and files only: no runtime, toolchain or HOL process.
"""
import argparse
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import allocation_analysis as an
import allocation_boundary as bd
import allocation_matrix as m
import allocation_schema as sc
import allocation_testbed as tb
import matrix_schema as ms
import task29_gate as gate
import task30_cases
import task31_cases
import task37_cases as cases
import test_allocation_grid as grid_tests
import test_allocation_matrix as matrix_tests

MATRIX = m.TASKS["task37-matrix"]
CLIENT = m.TASKS["task37-client"]
DOWNSTREAM = m.TASKS["task37-downstream"]
CAND = "c" * 40


class Pairs(unittest.TestCase):
    def test_legacy_tasks_keep_ten_pairs_and_task37_uses_three(self):
        self.assertEqual(m.PAIRS, 10)
        for name in ("task29b", "task30", "task31"):
            self.assertEqual(m.TASKS[name].pairs, 10, name)
        for task in (MATRIX, CLIENT, DOWNSTREAM):
            self.assertEqual(task.pairs, 3)
        self.assertEqual(m.TASK37_PAIRS, 3)

    def test_a_task_needs_an_ab_and_a_ba_pair(self):
        for pairs in (1, 0, True, 2.5):
            with self.assertRaisesRegex(sc.InvalidAllocation, "pair"):
                m.Task("x", "X", gate.CASES, "c.json", pairs=pairs)
        self.assertEqual(m.Task("x", "X", gate.CASES, "c.json",
                                pairs=2).pairs, 2)

    def test_the_grid_takes_the_pairs_of_its_task(self):
        def grid(task, pairs=None):
            return m.Grid(argparse.Namespace(
                task=task, pairs=pairs, repo=m.HERE.parents[3]))
        self.assertEqual(grid("task37-matrix").pairs, 3)
        self.assertEqual(grid("task37-client").pairs, 3)
        self.assertEqual(grid("task37-downstream").pairs, 3)
        self.assertEqual(grid("task30").pairs, 10)
        self.assertEqual(grid("task31").pairs, 10)
        self.assertEqual(grid("task29b").pairs, 10)
        self.assertEqual(grid("task37-client", 2).pairs, 2)
        self.assertEqual(grid("task30", 4).pairs, 4)

    def test_the_command_line_defaults_to_the_pairs_of_the_task(self):
        seen = {}

        def stop(args):
            seen["pairs"] = args.pairs
            return 0
        saved = m.run
        m.run = stop
        try:
            base = ["run", "--output", "o", "--candidate", CAND,
                    "--toolchain", "t", "--controls-receipt", "c"]
            self.assertEqual(m.main(base + ["--task", "task37-matrix"]), 0)
            self.assertIsNone(seen["pairs"])
            m.main(base + ["--task", "task37-matrix", "--pairs", "4"])
            self.assertEqual(seen["pairs"], 4)
            with self.assertRaisesRegex(sc.InvalidAllocation, "pair"):
                m.main(base + ["--pairs", "1"])
        finally:
            m.run = saved

    def test_an_unknown_task_is_refused(self):
        for name in ("task37-other", "task37", "task38"):
            with self.assertRaisesRegex(sc.InvalidAllocation, "unknown"):
                m.task_named(name)
            with self.assertRaisesRegex(sc.InvalidAllocation, "unknown"):
                m.task_of(dict(task=name))
            self.assertNotIn(name, m.TASKS)


class Cells(unittest.TestCase):
    def test_the_matrix_is_every_task29_and_task30_cell(self):
        self.assertEqual(MATRIX.cases, tuple(gate.CASES) +
                         tuple(task30_cases.CASES))
        keys = m.keys(MATRIX)
        self.assertEqual(len(keys), 306)
        self.assertEqual(len(keys), len(set(keys)))
        self.assertEqual(len(m.keys(m.TASKS["task29b"])) +
                         len(m.keys(m.TASKS["task30"])), 306)
        self.assertEqual(sum(n == 10000 for _, n in keys), 51)
        self.assertEqual(MATRIX.infeasible, frozenset())
        for case in MATRIX.cases:
            self.assertEqual(MATRIX.sizes(case), m.SIZES, case)
        self.assertIs(MATRIX.family, m.FAMILIES["MatrixPerformance.sml"])

    def test_the_client_cells_are_exactly_those_task31_allocates(self):
        self.assertEqual(m.keys(CLIENT), m.keys(m.TASKS["task31"]))
        self.assertEqual(len(m.keys(CLIENT)), 245)
        self.assertEqual(CLIENT.infeasible,
                         frozenset(task31_cases.INFEASIBLE_CELLS))
        self.assertIs(CLIENT.family, m.FAMILIES["ClientPerformance.sml"])
        self.assertFalse(any(c.startswith("downstream_")
                             for c in CLIENT.cases))

    def test_the_tasks_have_their_own_counts_files(self):
        self.assertEqual(MATRIX.iterations.name,
                         "allocation_iterations_task37_matrix.json")
        self.assertEqual(CLIENT.iterations.name,
                         "allocation_iterations_task37_client.json")
        self.assertEqual(len({t.iterations for t in (
            MATRIX, CLIENT, *(m.TASKS[n] for n in (
                "task29b", "task30", "task31")))}), 5)

    def test_the_counts_cover_the_cells_of_the_task_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            for task in (MATRIX, CLIENT):
                path = Path(tmp) / (task.name + ".json")
                counts = {"schema": "task29b-iterations-v1", "repeats": 4,
                          "steady": {m.name_of(*k): 8
                                     for k in m.keys(task)}}
                path.write_text(json.dumps(counts))
                self.assertEqual(m.load_iterations(path, task), counts)
                counts["steady"].popitem()
                path.write_text(json.dumps(counts))
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "incomplete"):
                    m.load_iterations(path, task)
        # the client's counts are not the matrix's
        counts = {"schema": "task29b-iterations-v1", "repeats": 4,
                  "steady": {m.name_of(*k): 8 for k in m.keys(CLIENT)}}
        path = Path(tempfile.mkdtemp()) / "c.json"
        try:
            path.write_text(json.dumps(counts))
            with self.assertRaisesRegex(sc.InvalidAllocation, "incomplete"):
                m.load_iterations(path, MATRIX)
        finally:
            path.unlink()
            path.parent.rmdir()

    def test_every_case_is_a_case_of_one_fixture_family(self):
        for task in (MATRIX, CLIENT):
            fixtures = {ms.EXPECTED_CASES[c]["fixture"] for c in task.cases}
            self.assertEqual(len(fixtures), 1)

    def test_the_case_views_are_the_task_modules_lists(self):
        self.assertEqual(cases.MATRIX_CASES, MATRIX.cases)
        self.assertEqual(cases.CLIENT_CASES, CLIENT.cases)
        self.assertEqual(len(gate.CASES), 27)
        self.assertEqual(len(task30_cases.CASES), 24)

    def test_the_task_is_in_the_grid_digest_and_the_header(self):
        with tempfile.TemporaryDirectory() as tmp:
            sandbox = tb.Sandbox(Path(tmp), 3)
            for task in (MATRIX, CLIENT):
                header = dict(sandbox.header(), task=task.name)
                self.assertEqual(m.task_of(header), task)
                self.assertNotEqual(
                    m.grid_digest(header),
                    m.grid_digest(dict(header, task="task30")))

    def test_the_harness_binds_the_case_modules_and_counts(self):
        for task in (MATRIX, CLIENT):
            inputs, fixtures = m.harness_files(task)
            names = {p.name for p in inputs}
            self.assertLessEqual({"task37_cases.py", "task31_cases.py",
                                  "task29_gate.py", "task30_cases.py",
                                  task.iterations.name}, names)
            self.assertEqual({p.name for p in fixtures if p.suffix ==
                              ".sml" and p.name.endswith("Allocation.sml")},
                             set(task.family.sources) & {
                                 "ClientAllocation.sml",
                                 "MatrixAllocation.sml"})
        legacy = {n: {p.name for p in m.harness_files(m.TASKS[n])[0]}
                  for n in ("task29b", "task30", "task31")}
        for names in legacy.values():
            self.assertNotIn("task37_cases.py", names)
        self.assertNotIn("task31_cases.py", legacy["task29b"])
        self.assertNotIn("task31_cases.py", legacy["task30"])
        self.assertIn("task31_cases.py", legacy["task31"])


def grid_of(task, pairs, change=None):
    cells, records, observed = set(), {}, {}
    for key in m.keys(task):
        base, cand, work = (change(key) if change else None) or (
            {"setup": 10}, {"setup": 10}, None)
        data = tb.experiment(base, cand, pairs=pairs, work=work)
        records[key] = dict(an.cell(*data, tb.STEADY), steady=tb.STEADY,
                            pairs=pairs)
        observed[key] = data
        cells.add(key)
    return cells, records, observed


class Decisions(unittest.TestCase):
    def test_three_pairs_pass_a_task37_task_row_by_row(self):
        for task in (MATRIX, CLIENT):
            out = m.assemble(*grid_of(task, 3), task=task, candidate=CAND)
            self.assertEqual((out["status"], out["complete"],
                              out["acceptance_pairs"]),
                             ("pass", True, True), task.name)
            self.assertEqual(len(out["rows"]), len(m.keys(task)))
            self.assertTrue(all(r["pairs"] == 3 and
                                r["decision"] == "pass"
                                for r in out["rows"]), task.name)

    def test_the_rule_of_another_task_does_not_accept_the_pairs(self):
        out = m.assemble(*grid_of(m.TASKS["task31"], 3),
                         task=m.TASKS["task31"], candidate=CAND)
        self.assertFalse(out["acceptance_pairs"])
        self.assertFalse(out["complete"])
        self.assertEqual(out["status"], "inconclusive")
        self.assertTrue(all(r["decision"] == "inconclusive"
                            for r in out["rows"]))
        out = m.assemble(*grid_of(MATRIX, 2), task=MATRIX, candidate=CAND)
        self.assertFalse(out["acceptance_pairs"])
        self.assertEqual(out["status"], "inconclusive")

    def test_legacy_tasks_still_need_ten_pairs(self):
        for name in ("task29b", "task30"):
            task = m.TASKS[name]
            ten = m.assemble(*grid_of(task, 10), task=task)
            self.assertTrue(ten["acceptance_pairs"], name)
            self.assertEqual(ten["status"], "pass", name)
            three = m.assemble(*grid_of(task, 3), task=task)
            self.assertFalse(three["acceptance_pairs"], name)
            self.assertEqual(three["status"], "inconclusive", name)

    def test_a_nondeterministic_cell_is_found_with_three_pairs(self):
        data = tb.experiment({"setup": 10}, {"setup": 10}, pairs=3)
        data[0][2]["candidate"] = tb.observation({"setup": 12})
        key = m.keys(CLIENT)[0]
        cells, records, observed = grid_of(CLIENT, 3)
        records[key] = dict(an.cell(*data, tb.STEADY), steady=tb.STEADY,
                            pairs=3)
        out = m.assemble(cells, records, observed, task=CLIENT,
                         candidate=CAND)
        self.assertTrue(any(r[0] == key[0] and r[1] == key[1] and
                            r[4] == "candidate"
                            for r in out["nondeterminism"]))
        self.assertNotEqual(out["status"], "pass")
        row = [r for r in out["rows"] if (r["case"], r["size"]) == key][0]
        self.assertNotEqual(row["decision"], "pass")
        # a control that differs from the baseline is found as well
        data = tb.experiment({"setup": 10}, {"setup": 10}, pairs=3,
                             ctrl=lambda i: tb.observation(
                                 {"setup": 10 + (i == 1)}))
        records[key] = dict(an.cell(*data, tb.STEADY), steady=tb.STEADY,
                            pairs=3)
        out = m.assemble(cells, records, observed, task=CLIENT,
                         candidate=CAND)
        self.assertTrue(any(r[4] == "control"
                            for r in out["nondeterminism"]))
        self.assertNotEqual(out["status"], "pass")


class Records(unittest.TestCase):
    def test_a_pairs_claim_that_is_not_the_rule_of_the_task_is_refused(self):
        def inventory(pairs, flag):
            return dict(pairs=pairs, acceptance_pairs=flag)
        m.check_pairs(inventory(3, True), MATRIX)
        m.check_pairs(inventory(2, False), MATRIX)
        m.check_pairs(inventory(10, True), m.TASKS["task30"])
        m.check_pairs(inventory(3, False), m.TASKS["task30"])
        for task, pairs, flag in ((MATRIX, 2, True), (CLIENT, 3, False),
                                  (m.TASKS["task30"], 3, True),
                                  (m.TASKS["task31"], 9, True)):
            with self.assertRaisesRegex(sc.InvalidAllocation, "acceptance"):
                m.check_pairs(inventory(pairs, flag), task)
        for bad in (None, 1, True, "3"):
            with self.assertRaisesRegex(sc.InvalidAllocation, "pair count"):
                m.check_pairs(dict(pairs=bad), MATRIX)
        # an older inventory without the flag is judged by its cells only
        m.check_pairs(dict(pairs=10), m.TASKS["task30"])

    def test_a_cell_of_other_pairs_than_the_header_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            sb = tb.Sandbox(Path(tmp) / "s", pairs=3)
            folder = Path(tmp) / "cell"
            sb.write_cell(folder)
            self.assertEqual(m.cell_data(folder, sb.bind())[0]["pairs"], 3)
            for pairs in (10, 4, 2):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "different inputs"):
                    m.cell_data(folder, sb.bind(pairs=pairs))

    def test_finish_refuses_an_inventory_that_misstates_its_pairs(self):
        with tempfile.TemporaryDirectory() as tmp:
            for name, pairs, flag in (("task37-client", 3, False),
                                      ("task37-matrix", 2, True),
                                      ("task30", 3, True)):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "acceptance"):
                    m.finish(Path(tmp), dict(
                        task=name, pairs=pairs, acceptance_pairs=flag,
                        runs=[]))



class Downstream(unittest.TestCase):
    def test_the_task_is_declared_by_its_family_not_by_its_name(self):
        self.assertEqual(
            sorted(c for c in DOWNSTREAM.cases),
            sorted(cases.DOWNSTREAM_CASES))
        self.assertTrue(DOWNSTREAM.family.closure)
        self.assertFalse(CLIENT.family.closure)
        self.assertFalse(MATRIX.family.closure)
        self.assertFalse(m.TASKS["task31"].family.closure)
        self.assertFalse(m.TASKS["task30"].family.closure)

    def test_the_family_installs_the_downstream_fixture(self):
        self.assertEqual(
            dict(DOWNSTREAM.family.files)["DownstreamAllocation.sml"],
            "Performance.sml")
        self.assertTrue(
            (m.HERE / "DownstreamAllocation.sml").is_file())

    def test_the_closure_record_normalises_the_private_directory(self):
        with tempfile.TemporaryDirectory() as raw:
            a, b = Path(raw) / "a", Path(raw) / "b"
            for d in (a, b):
                d.mkdir()
                (d / "x.uo").write_bytes(
                    b"head " + str(d.resolve()).encode() + b" tail")
                (d / "y.sml").write_bytes(b"copy")
            def result(d):
                return dict(modules=["x"], roots=["r"], products={
                    "x.uo": dict(source="s/x.uo"),
                    "y.sml": dict(source="s/y.sml")})
            ra = m.closure_record(result(a), a)
            rb = m.closure_record(result(b), b)
            self.assertEqual(ra, rb)
            (b / "y.sml").write_bytes(b"other")
            self.assertNotEqual(ra, m.closure_record(result(b), b))

    def test_install_private_is_closure_free_for_legacy_families(self):
        for name in ("task30", "task31", "task37-matrix", "task37-client"):
            grid = m.Grid(argparse.Namespace(
                task=name, pairs=None, repo=m.HERE.parents[3]))
            with tempfile.TemporaryDirectory() as raw, \
                    mock.patch.object(m.rp, "install_fixtures"):
                d = Path(raw)
                (d / "Holmakefile").write_text("")
                self.assertIsNone(grid.install_private(d, []), name)

    def test_the_closure_is_installed_for_the_downstream_family(self):
        grid = m.Grid(argparse.Namespace(
            task="task37-downstream", pairs=None,
            repo=m.HERE.parents[3]))
        grid.hol = Path("/hol")
        sources = [dict(git_path="src/simp/src/Cond_rewr.sml")]
        with tempfile.TemporaryDirectory() as raw, \
                mock.patch.object(m.rp, "install_fixtures"), \
                mock.patch("client_dependencies.install",
                           return_value="R") as ins:
            d = Path(raw)
            (d / "Holmakefile").write_text("")
            self.assertEqual(grid.install_private(d, sources), "R")
            ins.assert_called_once_with(Path("/hol"), d, {"Cond_rewr"})
            self.assertIn("paired.exe: Performance.uo",
                          (d / "Holmakefile").read_text())


DEP = "Dep.sml"
HEAP = "src/Heap1.sml"
HEAP_UO = "src/Heap1.uo"


class ClosureReceipts(unittest.TestCase):
    """check_receipt of a closure family (the downstream cells): a loaded
    shared file, or a product's source, that differs between baseline and
    candidate must be a reviewed boundary file; the closure installed
    privately is checked per side."""

    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.sb = tb.Sandbox(Path(tmp.name), pairs=3)
        self.repo = self.sb.repo
        for directory in self.sb.private.values():
            (directory / DEP).write_text("val dep = 1\n")

    def header(self, changed=(), files=(), source="generated", seal=None,
               prefixes=None, closure=True):
        sides = {side: dict(modules=["Dep"], roots=[], products={
            DEP: dict(source=source, **(seal or tb.seal(
                directory / DEP)))}) for side, directory in
            self.sb.private.items()}
        boundary = dict(
            schema=bd.SCHEMA, changed=0,
            manifest_prefixes=list(tb.PREFIXES if prefixes is None
                                   else prefixes),
            files=[dict(path=f, blob="1" * 40) for f in files])
        found = dict(boundary=boundary)
        if closure:
            found["closure"] = dict(changed=list(changed), sides=sides,
                                    inputs={})
        return found

    def check(self, edit=None, side="candidate", **header):
        dep = str(self.sb.private[side] / DEP)

        def mutate(events):
            at = events.index(["use", str(self.sb.private[side] /
                                          "MatrixSupport.sml")])
            events[at:at] = [["use", dep], ["used", dep]]
            events.insert(len(events) - 1, ["loaded", dep])
        receipt = self.sb.receipt("candidate", side, 0, 1, mutate=mutate)
        receipt["paths"].update(self.sb.paths([dep]))
        if edit is not None:
            edit(receipt)
        meta = dict(self.sb.bind(**self.header(**header)),
                    schema=m.SCHEMA)
        return m.check_receipt(receipt, meta, "candidate")

    def refused(self, message, *args, **kw):
        with self.assertRaisesRegex(sc.InvalidAllocation, message):
            self.check(*args, **kw)

    def theory(self, script=True, built=True, seal=None, name="xTheory.sml"):
        """check_receipt of a process that loaded the file `name` of a
        theory built by the private Holmake (below .hol/objs), whose
        script is selected or not; `built` is its post-build record."""
        side = "candidate"
        theory = self.sb.private[side] / ".hol/objs" / name
        theory.parent.mkdir(parents=True, exist_ok=True)
        theory.write_text("structure xTheory = struct end\n")
        path = str(theory)

        def mutate(events):
            at = events.index(["use", str(self.sb.private[side] /
                                          "MatrixSupport.sml")])
            events[at:at] = [["use", path], ["used", path]]
            events.insert(len(events) - 1, ["loaded", path])
        receipt = self.sb.receipt("candidate", side, 0, 1, mutate=mutate)
        receipt["paths"].update(self.sb.paths([path]))
        if built:
            receipt["built"] = {".hol/objs/" + name: seal or tb.seal(theory)}
        sources = self.sb.sources()
        if script:
            sources[side] = dict(sources[side], **{
                "xScript.sml": dict(sha256="1" * 64, bytes=1)})
        meta = dict(self.sb.bind(sources=sources, **self.header()),
                    schema=m.SCHEMA)
        return m.check_receipt(receipt, meta, "candidate")

    def test_the_theory_of_a_selected_script_is_judged_by_its_script(self):
        for name in ("xTheory.sml", "xTheory.sig", "xTheory.uo",
                     "xTheory.ui", "xTheory.dat"):
            with self.subTest(name):
                self.assertEqual(self.theory(name=name)["steady"],
                                 tb.STEADY)

    def test_a_theory_is_refused_without_its_selected_script(self):
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "wrong selected source: xTheory.sml"):
            self.theory(script=False)

    def test_a_theory_must_have_the_seal_of_the_post_build_record(self):
        other = dict(sha256="0" * 64, bytes=3)
        for kw in (dict(seal=other), dict(built=False)):
            with self.subTest(**kw), self.assertRaisesRegex(
                    sc.InvalidAllocation,
                    "wrong selected source: xTheory.sml"):
                self.theory(**kw)

    def test_the_processes_of_a_side_agree_on_the_built_tree(self):
        folder = self.sb.root / "cellfolder"
        self.sb.write_cell(folder)
        first = sorted((folder / "candidate").glob("pair-*.json.gz"))[0]
        tb.rewrite(first, lambda r: r.update(
            built={".hol/objs/xTheory.sml": dict(sha256="1" * 64,
                                                 bytes=1)}))
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "built differently"):
            m.cell_data(folder, self.sb.bind())

    def test_the_binding_carries_the_boundary_files_of_the_closure(self):
        bound = self.sb.bind(**self.header(files=[HEAP]))
        self.assertEqual(bound["closure"]["boundary_files"],
                         {HEAP: "1" * 40})
        self.assertEqual(sorted(bound["closure"]),
                         ["boundary_files", "changed", "sides"])

    def test_a_clean_closure_receipt_is_accepted(self):
        self.assertEqual(self.check()["steady"], tb.STEADY)
        # a changed file that the reviewed boundary lists is accepted,
        # also with its product beside it
        found = self.check(changed=[HEAP, HEAP_UO, "src/simp/src/X.sml"],
                           files=[HEAP, HEAP_UO])
        self.assertEqual(found["steady"], tb.STEADY)

    def test_a_changed_loaded_file_outside_the_boundary_is_refused(self):
        for changed, files in (([HEAP], []), ([HEAP], ["other.sml"]),
                               ([HEAP_UO], [HEAP]),
                               ([HEAP, HEAP_UO], [HEAP])):
            with self.subTest(changed=changed, files=files):
                self.refused("not a reviewed boundary file",
                             changed=changed, files=files)

    def test_a_product_beside_a_loaded_file_is_checked_too(self):
        self.refused("not a reviewed boundary file", changed=[HEAP_UO])

    def test_a_closure_product_must_have_the_sealed_content(self):
        self.refused("wrong selected source", seal=dict(
            sha256="0" * 64, bytes=12))
        self.refused("wrong selected source", seal=dict(
            sha256=tb.seal(self.sb.private["candidate"] / DEP)["sha256"],
            bytes=1))

    def test_the_closure_of_the_other_side_is_not_this_sides(self):
        other = tb.seal(self.sb.private["baseline"] / DEP)
        (self.sb.private["candidate"] / DEP).write_text("val dep = 2\n")
        self.assertEqual(other, tb.seal(self.sb.private["baseline"] / DEP))
        # the sides' products were sealed with the new content: accepted;
        # sealed with the baseline's content: refused
        self.check()
        self.refused("wrong selected source", seal=other)

    def test_a_shared_input_outside_the_toolchain_is_refused(self):
        def outside(receipt):
            for info in receipt["paths"].values():
                if info["physical"].endswith("Heap1.sml"):
                    info["physical"] = "/elsewhere/Heap1.sml"
        self.refused("shared input outside the toolchain", outside)

        def related(receipt):
            for info in receipt["paths"].values():
                if info["related_products"]:
                    info["related_products"] = {
                        "/elsewhere/Heap1.uo": dict(sha256="0" * 64,
                                                    bytes=1)}
        self.refused("shared input outside the toolchain", related)

    def test_a_shared_simp_load_is_refused(self):
        def simp(receipt):
            for info in receipt["paths"].values():
                if info["physical"].endswith("Heap1.sml"):
                    info["physical"] = str(self.repo /
                                           "src/simp/src/Foo.sml")
        self.refused("shared input outside the toolchain", simp)

    def test_a_changed_closure_product_source_is_checked(self):
        source = str(self.repo / HEAP)
        self.refused("closure product", changed=[HEAP], source=source)
        self.refused("closure product", changed=["src/simp/src/X.sml"],
                     source=str(self.repo / "src/simp/src/X.sml"))
        self.refused("outside the toolchain", source="/elsewhere/X.sml")
        self.check(changed=[HEAP], files=[HEAP], source=source)
        # a source that did not change, and a generated rule that names no
        # path, are not changed shared files
        self.check(changed=["other"], source=source)
        self.check(changed=[HEAP], files=[HEAP],
                   source="generated dependency rules")

    def test_the_legacy_prefix_refusal_still_applies_without_a_closure(self):
        self.assertEqual(self.sb.bind(
            **self.header(closure=False)).get("closure"), None)

        sb = self.sb
        receipt = sb.receipt("candidate", "candidate", 0, 1)
        meta = dict(sb.bind(**self.header(closure=False, prefixes=["src/"])),
                    schema=m.SCHEMA)
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "under the boundary prefix"):
            m.check_receipt(receipt, meta, "candidate")
        meta = dict(sb.bind(**self.header(closure=False, prefixes=[])),
                    schema=m.SCHEMA)
        m.check_receipt(receipt, meta, "candidate")

    def test_the_closure_is_in_the_digest_the_binding_and_the_settings(self):
        header = dict(self.sb.header(), **self.header(files=[HEAP]),
                      task="task37-downstream")
        digest = m.grid_digest(header)
        self.assertNotEqual(digest, m.grid_digest(
            {k: v for k, v in header.items() if k != "closure"}))
        other = json.loads(json.dumps(header))
        other["closure"]["changed"] = ["x"]
        self.assertNotEqual(digest, m.grid_digest(other))
        other = json.loads(json.dumps(header))
        other["closure"]["sides"]["candidate"]["modules"] = ["X"]
        self.assertNotEqual(digest, m.grid_digest(other))
        self.assertEqual(m.binding(header, tb.CASE, tb.SIZE)["closure"][
            "sides"], header["closure"]["sides"])
        self.assertIn("closure", m.changed_settings(
            header, other))
        self.assertNotIn("closure", m.changed_settings(header, header))
        self.assertIn("closure", m.changed_settings(
            {k: v for k, v in header.items() if k != "closure"}, header))
        # a cell measured under another closure is refused
        folder = Path(self.sb.root) / "cell"
        self.sb.write_cell(folder, **self.header(files=[HEAP]))
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "different inputs"):
            m.cell_data(folder, self.sb.bind(**self.header(
                files=[HEAP], changed=["x"])))


class ClosureProducts(unittest.TestCase):
    """The closure guard compares the sources a changed-path list names with
    the compiled products a process loads: `source_of` maps a product to
    its source first, and a shared product of a module the closure installs
    privately is refused."""
    REPO = Path("/repo")

    def meta(self, changed=(), files=(), modules=("Dep",)):
        return dict(closure=dict(
            changed=list(changed), boundary_files={f: "1" * 40
                                                   for f in files},
            sides={side: dict(modules=list(modules), roots=[], products={})
                   for side in ("baseline", "candidate", "control")}))

    def check(self, path, loaded=False, **meta):
        return m.check_changed_input(self.REPO, self.REPO / path,
                                     self.meta(**meta), "x", loaded)

    def test_a_product_maps_to_its_source(self):
        for product, source in (
                ("src/x/.hol/objs/FooTheory.uo", "src/x/FooScript.sml"),
                ("src/x/.hol/objs/FooTheory.ui", "src/x/FooScript.sml"),
                ("src/x/.hol/objs/FooTheory.dat", "src/x/FooScript.sml"),
                ("src/x/.hol/objs/FooTheory.sml", "src/x/FooScript.sml"),
                ("src/x/FooTheory.uo", "src/x/FooScript.sml"),
                ("src/x/Foo.uo", "src/x/Foo.sml"),
                ("src/x/Foo.ui", "src/x/Foo.sig"),
                ("src/x/.hol/objs/Foo.uo", "src/x/Foo.sml"),
                ("src/x/Foo.sml", "src/x/Foo.sml"),
                ("src/x/Foo.sig", "src/x/Foo.sig"),
                ("src/x/Theory.sml", "src/x/Theory.sml"),
                ("sigobj/Foo.uo", "sigobj/Foo.sml")):
            with self.subTest(product=product):
                self.assertEqual(m.source_of(product), source)

    def test_a_module_without_a_signature_is_covered_by_its_uo(self):
        # no `.sig` means no `.ui` is ever loaded: the `.uo` stands for the
        # `.sml`; a module with both has each source covered by its own
        # product
        self.assertEqual(m.source_of("src/x/NoSig.uo"), "src/x/NoSig.sml")
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "not a reviewed boundary"):
            self.check("src/x/NoSig.uo", changed=["src/x/NoSig.sml"])
        self.check("src/x/NoSig.uo", changed=["src/x/Other.sig"])

    def test_a_changed_source_is_found_through_the_product_loaded(self):
        for product, source in (
                ("src/x/.hol/objs/FooTheory.uo", "src/x/FooScript.sml"),
                ("src/x/.hol/objs/FooTheory.dat", "src/x/FooScript.sml"),
                ("src/x/Foo.uo", "src/x/Foo.sml"),
                ("src/x/Foo.ui", "src/x/Foo.sig")):
            with self.subTest(product=product):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "not a reviewed boundary"):
                    self.check(product, changed=[source])
                self.check(product, changed=[source], files=[source])
                self.check(product, changed=["src/x/Other.sml"])

    def test_a_loaded_product_of_a_recompiled_module_is_refused(self):
        for product in ("src/x/Dep.uo", "src/x/Dep.ui",
                        "src/x/.hol/objs/Dep.uo", "sigobj/Dep.sml"):
            with self.subTest(product=product):
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "installs privately"):
                    self.check(product, loaded=True)
                # the origin of a product the closure copies is no load
                self.check(product, loaded=False)
        self.check("src/x/Heap1.uo", loaded=True)

    def test_a_module_of_either_side_counts(self):
        meta = self.meta(modules=())
        meta["closure"]["sides"]["candidate"]["modules"] = ["Dep"]
        with self.assertRaisesRegex(sc.InvalidAllocation, "installs"):
            m.check_changed_input(self.REPO, self.REPO / "src/Dep.uo",
                                  meta, "x", True)


class Closures(unittest.TestCase):
    """Grid.make_closure and make_job for a closure family, over the
    stubbed checkout of test_allocation_grid.Jobs."""
    REVS = grid_tests.Jobs.REVS

    def setUp(self):
        grid_tests.Jobs.setUp(self)
        grid = self.grid
        grid.task = DOWNSTREAM
        grid.args = argparse.Namespace(baseline="a" * 40,
                                       candidate="b" * 40)
        grid.repo = Path(self.tmp.name) / "repo"
        self.results = {}
        self.records = {}
        self.inputs = {}
        patches = [mock.patch.object(m.bd, "changed_paths",
                                     return_value=["p"]),
                   mock.patch.object(m, "closure_record",
                                     side_effect=self.record)]
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)
        grid.install_private = self.install

    def record(self, result, directory):
        return result["record"]

    def install(self, directory, sources):
        label = directory.name.replace("closure-", "")
        side = {v: k for k, v in m.SIDES.items()}.get(label, label)
        return dict(record=self.records.get(side, dict(modules=["M"])),
                    inputs=self.inputs.get(side, {"/hol/x": [1]}))

    def test_the_closure_is_made_per_side_with_its_inputs(self):
        closure = self.grid.make_closure()
        self.assertEqual(sorted(closure["sides"]), sorted(m.SIDES))
        self.assertEqual((closure["changed"], closure["inputs"]),
                         (["p"], {"/hol/x": [1]}))

    def test_a_control_that_is_not_the_baselines_copy_is_refused(self):
        self.records["control"] = dict(modules=["other"])
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "control closure is not a copy"):
            self.grid.make_closure()

    def test_an_input_that_changed_between_sides_is_refused(self):
        self.inputs["candidate"] = {"/hol/x": [2]}
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "closure input changed between sides"):
            self.grid.make_closure()

    def test_a_job_must_install_the_closure_of_the_grid(self):
        self.grid.closure = self.grid.make_closure()
        self.assertTrue(self.grid.make_job(0).dirs)
        self.records["candidate"] = dict(modules=["other"])
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "installed closure differs from the "
                                    "grid's"):
            self.grid.make_job(1)


if __name__ == "__main__":
    unittest.main()
