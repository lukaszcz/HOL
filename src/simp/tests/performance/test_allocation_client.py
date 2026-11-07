#!/usr/bin/env python3
"""TASK31 in the allocation matrix: the client fixture family, the cells of
`task31`, its predeclared counts and the rows of its decisions.

Synthetic receipts and files only, as test_allocation_task.py: no runtime,
toolchain or HOL process.
"""
import json
from pathlib import Path
import re
import tempfile
import unittest
from unittest import mock

import acceptance as a
import allocation_analysis as an
import allocation_matrix as m
import allocation_schema as sc
import allocation_testbed as tb
import matrix_schema as ms
import task31_cases as cases
import task31_iterations as it

TASK31 = m.TASKS["task31"]
HERE = m.HERE
# The driver of MatrixAllocation.sml, which ClientAllocation.sml repeats.
DRIVER = "(* Build every foreign closure"


def declarations(text):
    """Top-level declarations by their first line: up to the next line that
    starts another one at column 0 (a comment line starts none)."""
    found, current = {}, None
    for line in text.split("\n"):
        if re.match(r"(fun|val|type|exception|\(\*) ", line):
            current = found.setdefault(line, [])
        if current is not None:
            current.append(line)
    return {k: [l for l in v if l.strip()] for k, v in found.items()}


def client_lines(text):
    return [l for l in text.split("\n") if not l.rstrip().endswith(
        "(*alloc*)")]


class Scope(unittest.TestCase):
    def test_the_cases_are_the_client_traversal_and_tactic_cases(self):
        clients = [c for c, v in ms.EXPECTED_CASES.items()
                   if v["fixture"] == "ClientPerformance.sml" and
                   c.startswith(("traversal_", "tactic_"))]
        self.assertEqual(sorted(cases.CASES), sorted(clients))
        self.assertEqual(len(cases.CASES), 11 + 42)
        self.assertEqual(TASK31.cases, cases.CASES)
        self.assertEqual(len(set(cases.CASES)), len(cases.CASES))
        self.assertFalse(any(c.startswith("downstream_")
                             for c in cases.CASES))

    def test_every_size_is_up_to_1000_but_the_light_families(self):
        found = m.keys(TASK31)
        self.assertEqual(len(found), 245)
        light = tuple("tactic_%s_" % f for f in cases.LIGHT_FAMILIES)
        big = [k for k in found if k[1] > 1000]
        self.assertEqual(sorted(big), sorted(
            (c, 10000) for c in cases.CASES if c.startswith(light)))
        self.assertEqual(len(big), 9)
        for case in cases.CASES:
            sizes = TASK31.sizes(case)
            if case.startswith("traversal_"):
                self.assertIn(sizes, ((0,), (0, 1, 10, 100)), case)
            else:
                self.assertEqual(sizes[:5], (0, 1, 10, 100, 1000), case)

    def test_the_infeasible_cells_are_the_33_heavy_ones_and_not_run(self):
        self.assertEqual(len(cases.INFEASIBLE), 33)
        self.assertFalse(set(cases.INFEASIBLE) & set(m.keys(TASK31)))
        every = {(c, n) for c in cases.CASES
                 for n in TASK31.every_size(c)}
        self.assertEqual(every, set(m.keys(TASK31)) | set(cases.INFEASIBLE))
        self.assertEqual({n for _, n in cases.INFEASIBLE}, {10000})
        light = tuple("tactic_%s_" % f for f in cases.LIGHT_FAMILIES)
        self.assertFalse([c for c, _ in cases.INFEASIBLE
                          if c.startswith(light)])

    def test_the_infeasible_cells_must_be_cells_of_the_task(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "no cell"):
            m.Task("x", "X", cases.CASES, "c.json",
                   [("tactic_full_reuse", 7)])
        with self.assertRaisesRegex(sc.InvalidAllocation, "no cell"):
            m.Task("x", "X", cases.CASES, "c.json",
                   [("traversal_deep", 10000)])

    def test_the_task_is_named_and_asks_for_rows(self):
        self.assertIs(m.task_named("task31"), TASK31)
        self.assertIs(m.task_of(dict(task="task31")), TASK31)
        self.assertEqual(TASK31.label, "TASK31")
        self.assertTrue(TASK31.rows)
        self.assertFalse(m.TASKS["task29b"].rows or m.TASKS["task30"].rows)

    def test_the_other_tasks_keep_every_size(self):
        for name in ("task29b", "task30"):
            task = m.TASKS[name]
            self.assertEqual(task.infeasible, frozenset())
            self.assertTrue(all(task.sizes(c) == m.SIZES
                                for c in task.cases))


class Families(unittest.TestCase):
    def test_the_fixture_of_the_cases_chooses_the_family(self):
        self.assertEqual(set(m.FAMILIES), {"MatrixPerformance.sml",
                                           "ClientPerformance.sml"})
        for name in ("task29b", "task30"):
            self.assertIs(m.TASKS[name].family,
                          m.FAMILIES["MatrixPerformance.sml"])
        self.assertIs(TASK31.family, m.FAMILIES["ClientPerformance.sml"])
        self.assertEqual(TASK31.family.sources,
                         ("ClientAllocation.sml", "MatrixSupport.sml"))
        self.assertEqual(m.FAMILIES["MatrixPerformance.sml"].sources,
                         m.FIXTURES)
        self.assertTrue(TASK31.family.dependencies)
        self.assertFalse(m.TASKS["task30"].family.dependencies)

    def test_both_families_install_the_names_the_protocol_checks(self):
        for family in m.FAMILIES.values():
            self.assertEqual(tuple(t for _, t in family.files), m.INSTALLED)
            for source in family.sources:
                self.assertTrue((HERE / source).is_file(), source)

    def test_a_task_of_two_families_is_refused(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "one fixture"):
            m.Task("x", "X", ("traversal_deep", "exclude_empty"), "c.json")

    def test_the_harness_binds_the_family_and_its_case_lists(self):
        def names(task):
            inputs, fixtures = m.harness_files(task)
            return ({p.name for p in inputs}, {p.name for p in fixtures})
        inputs, fixtures = names(TASK31)
        self.assertIn("allocation_iterations_task31.json", inputs)
        self.assertIn("ClientAllocation.sml", inputs | fixtures)
        self.assertNotIn("MatrixAllocation.sml", inputs | fixtures)
        self.assertLessEqual({"task31_cases.py", "client_dependencies.py",
                              "MatrixSupport.sml"}, inputs)
        inputs, fixtures = names(m.TASKS["task30"])
        self.assertIn("MatrixAllocation.sml", inputs)
        self.assertNotIn("ClientAllocation.sml", inputs | fixtures)


class Fixture(unittest.TestCase):
    """ClientAllocation.sml is the client workloads inside the driver of
    MatrixAllocation.sml, and nothing else."""

    @classmethod
    def setUpClass(cls):
        cls.alloc = (HERE / "ClientAllocation.sml").read_text()
        cls.matrix = (HERE / "MatrixAllocation.sml").read_text()
        cls.timing = (HERE / "ClientPerformance.sml").read_text()

    def test_the_driver_is_that_of_the_matrix_fixture_word_for_word(self):
        self.assertEqual(self.alloc[self.alloc.index(DRIVER):],
                         self.matrix[self.matrix.index(DRIVER):])

    def test_the_workloads_are_those_of_the_timing_fixture(self):
        ours = declarations("\n".join(client_lines(self.alloc)))
        theirs = declarations(self.timing)
        for first in ("val sink = ref 0", "fun consume () = sink := !sink + 1",
                      "fun same expected actual =",
                      "fun verify expected actual =",
                      "type workload = {run:unit -> unit, "
                      "verify:unit -> unit}",
                      "fun conversion stage make input expected : workload"
                      " = let"):
            self.assertIn(first, theirs, first)
            self.assertEqual(ours[first], theirs[first], first)
        for name in ("traversal", "tacticWork", "dependencyWork"):
            found = [k for k in theirs if k.startswith("fun %s " % name)]
            self.assertEqual(len(found), 1, name)
            self.assertEqual(ours[found[0]], theirs[found[0]], name)
        choose = [l for l in theirs["fun choose () ="] if "downstream"
                  not in l]
        self.assertEqual(ours["fun choose () ="], choose)

    def test_only_the_marked_lines_are_added_to_the_workloads(self):
        marked = [l for l in self.alloc.split("\n")
                  if l.rstrip().endswith("(*alloc*)")]
        self.assertEqual(len(marked), 2 + 4 + 4)
        retaining = [l for l in marked if "retaining" in l]
        self.assertEqual(len(retaining), 3)
        # the result and a use of it for each of conversion, tactic and
        # dependency work
        self.assertEqual(sum("thmText (!proof)" in l for l in marked), 3)
        self.assertEqual(sum("ignore ((!slot) input)" in l
                             for l in marked), 1)
        self.assertEqual(sum("apply ()" in l for l in marked), 2)

    def test_the_timing_driver_and_downstream_are_not_copied(self):
        for word in ("downstream", "RuntimeMetrics", "calibrate",
                     "PERF_SAMPLES", "PERF_SECONDS", "measure"):
            self.assertNotIn(word, self.alloc.replace(
                "`downstream`", "").replace("RuntimeMetrics)", ""), word)

    def test_the_fixture_makes_one_workload_of_the_case_and_size(self):
        self.assertIn('val label = Paired.env "PERF_CASE"', self.alloc)
        self.assertIn("val selected = label", self.alloc)
        self.assertIn("val workloadSize = size", self.alloc)
        self.assertIn("fun workload _ _ = let", self.alloc)
        self.assertIn("MatrixSupport.basic run check", self.alloc)

    def test_the_sources_follow_the_style(self):
        for name in ("ClientAllocation.sml", "task31_cases.py",
                     "task31_iterations.py", "test_allocation_client.py"):
            for number, line in enumerate(
                    (HERE / name).read_text().split("\n")):
                self.assertNotIn("\t", line, (name, number))
                self.assertEqual(line, line.rstrip(), (name, number))
                self.assertLess(len(line), 80, (name, number))


class Counts(unittest.TestCase):
    def test_the_committed_counts_are_those_of_the_rule(self):
        counts = m.load_iterations(task=TASK31)
        self.assertEqual(counts, json.loads(json.dumps(
            it.document(m.keys(TASK31)))))
        self.assertEqual(len(counts["steady"]), 245)
        self.assertEqual(counts["repeats"], 4)
        self.assertEqual(counts["schema"], "task29b-iterations-v1")
        self.assertEqual(TASK31.iterations, it.OUTPUT)

    def test_the_rule_cuts_only_the_costly_cells_at_1000(self):
        steady = m.load_iterations(task=TASK31)["steady"]
        small = {k: v for k, v in steady.items() if v == 4}
        self.assertEqual(sorted(small), sorted(
            "tactic_%s_%s-1000" % (f, s)
            for f in ("global", "req0", "reqd", "req0_reqd", "reqd_req0")
            for s in ("reuse", "complete")))
        for key, value in steady.items():
            size = int(key.rsplit("-", 1)[1])
            if size <= 100:
                self.assertEqual(value, 32, key)
            elif value != 4:
                self.assertIn(value, (8, 16), key)

    def test_every_cell_stays_inside_the_budget_of_a_process(self):
        for (case, size) in m.keys(TASK31):
            count = it.steady(case, size)
            self.assertGreaterEqual(count, it.MINIMUM)
            if case.endswith(("_reuse", "_complete")):
                self.assertLessEqual(
                    count * it.REPEATS * it.apply_cost(case, size),
                    it.BUDGET, (case, size))

    def test_the_task_has_its_own_counts_and_they_are_not_the_others(self):
        self.assertFalse(set(m.load_iterations(task=TASK31)["steady"]) &
                         set(m.load_iterations(task=m.TASKS["task30"])[
                             "steady"]))
        with self.assertRaisesRegex(sc.InvalidAllocation, "incomplete"):
            m.load_iterations(TASK31.iterations)
        with self.assertRaisesRegex(sc.InvalidAllocation, "incomplete"):
            m.load_iterations(m.TASKS["task30"].iterations, TASK31)

    def test_the_full_run_is_projected_at_about_ten_hours(self):
        hours = it.estimate(m.keys(TASK31))
        self.assertGreater(hours, 8)
        self.assertLess(hours, 14)

    def test_the_generator_writes_the_committed_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "counts.json"
            self.assertEqual(it.main(["--output", str(out)]), 0)
            self.assertEqual(out.read_bytes(), it.OUTPUT.read_bytes())


def record(base, cand, work=None, pairs=10, ctrl=None):
    data = tb.experiment(base, cand, ctrl, pairs=pairs, work=work)
    return (dict(an.cell(*data, tb.STEADY), steady=tb.STEADY, pairs=pairs),
            data)


def grid_of(task, change=None, pairs=10):
    """Identical sides in every cell of the task; change(key) may give a
    cell its own (base, cand, work)."""
    cells, records, observed = set(), {}, {}
    for key in m.keys(task):
        base, cand, work = (change(key) if change else None) or (
            {"setup": 10}, {"setup": 10}, None)
        records[key], observed[key] = record(base, cand, work, pairs)
        cells.add(key)
    return cells, records, observed


class Decisions(unittest.TestCase):
    def test_the_whole_grid_of_identical_sides_passes_row_by_row(self):
        out = m.assemble(*grid_of(TASK31), task=TASK31)
        self.assertEqual((out["status"], out["complete"],
                          out["acceptance_pairs"]), ("pass", True, True))
        self.assertEqual(m.status_code(out), 0)
        self.assertEqual(list(out["rows"]),
                         [m.name_of(*k) for k in m.keys(TASK31)])
        for name, row in out["rows"].items():
            case, size = name.rsplit("-", 1)
            self.assertEqual(row, dict(case=case, size=int(size), pairs=10,
                                       status="pass", work=None), name)
        self.assertEqual(len(out["cases"]), 53)
        self.assertEqual(out["unresolved"], [])
        self.assertEqual(out["infeasible"], sorted(
            m.name_of(*k) for k in cases.INFEASIBLE))
        self.assertEqual(len(out["infeasible"]), 33)

    def test_the_slopes_follow_the_sizes_of_each_case(self):
        out = m.assemble(*grid_of(TASK31), task=TASK31)
        for case, record in out["cases"].items():
            sizes = TASK31.sizes(case)
            self.assertEqual(sorted(map(int, record["cells"])),
                             sorted(sizes), case)
            rows = record["slopes"]["setup"]["total"]
            self.assertEqual([r["sizes"] for r in rows],
                             [[lo, hi] for lo, hi in zip(sizes, sizes[1:])],
                             case)
        self.assertEqual(
            out["cases"]["traversal_construct"]["slopes"]["setup"]["total"],
            [])

    def test_a_failing_cell_is_a_failing_row_and_fails_the_grid(self):
        bad = ("tactic_asm_complete", 1000)
        out = m.assemble(*grid_of(TASK31, lambda k: (
            {"setup": 10}, {"setup": 11}, None) if k == bad else None),
            task=TASK31)
        self.assertEqual(out["status"], "fail")
        self.assertEqual(m.status_code(out), 1)
        self.assertEqual(out["rows"][m.name_of(*bad)]["status"], "fail")
        others = [r["status"] for n, r in out["rows"].items()
                  if n != m.name_of(*bad)]
        self.assertEqual(set(others), {"pass"})

    def test_a_cell_whose_control_varies_is_inconclusive(self):
        base, cand = {"setup": 10}, {"setup": 10}
        data = tb.experiment(base, cand, lambda i: tb.observation(
            {"setup": 10 + (i == 0)}))
        key = ("traversal_deep", 100)
        cells, records, observed = grid_of(TASK31)
        records[key] = dict(an.cell(*data, tb.STEADY), steady=tb.STEADY,
                            pairs=10)
        out = m.assemble(cells, records, observed, task=TASK31)
        self.assertEqual(out["rows"][m.name_of(*key)]["status"],
                         "inconclusive")
        self.assertEqual(out["status"], "inconclusive")

    def test_the_work_row_is_beside_the_words(self):
        work, other = tb.structural(), tb.structural(
            first=tb.WORK_TEXT.replace("=1", "=2", 1))
        key = ("tactic_full_reuse", 100)
        out = m.assemble(*grid_of(TASK31, lambda k: (
            {"setup": 10}, {"setup": 10}, work if k != key else (
                work, other))), task=TASK31)
        rows = out["rows"]
        self.assertEqual(rows[m.name_of(*key)]["work"], "differs")
        self.assertEqual(rows[m.name_of(*key)]["status"], "pass")
        self.assertEqual({r["work"] for n, r in rows.items()
                          if n != m.name_of(*key)}, {"equal"})
        self.assertEqual(out["status"], "pass")
        self.assertEqual(out["work_status"], "differs")

    def test_a_partial_run_has_rows_for_its_cells_only(self):
        cells, records, observed = grid_of(TASK31)
        keep = {("traversal_deep", 0), ("tactic_asm_complete", 10000)}
        out = m.assemble(keep, {k: records[k] for k in keep},
                         {k: observed[k] for k in keep}, task=TASK31)
        self.assertEqual(sorted(out["rows"]), sorted(
            m.name_of(*k) for k in keep))
        self.assertFalse(out["complete"])
        self.assertEqual(out["status"], "inconclusive")
        self.assertEqual(len(out["infeasible"]), 33)

    def test_a_cell_without_an_analysis_is_an_unresolved_row(self):
        keep = {("traversal_deep", 0), ("traversal_deep", 1)}
        cells, records, observed = grid_of(TASK31)
        out = m.assemble(keep, {("traversal_deep", 0):
                                records["traversal_deep", 0]}, {},
                         task=TASK31)
        self.assertEqual(out["unresolved"], ["traversal_deep-1"])
        self.assertEqual(out["rows"]["traversal_deep-1"], dict(
            case="traversal_deep", size=1, pairs=None,
            status="unresolved", work=None))
        self.assertEqual(out["rows"]["traversal_deep-0"]["status"], "pass")

    def test_a_smoke_never_passes_but_its_rows_say_what_they_are(self):
        out = m.assemble(*grid_of(TASK31, pairs=2), task=TASK31)
        self.assertFalse(out["acceptance_pairs"])
        self.assertEqual(out["status"], "inconclusive")
        self.assertEqual({r["pairs"] for r in out["rows"].values()}, {2})
        self.assertEqual({r["status"] for r in out["rows"].values()},
                         {"pass"})

    def test_the_other_tasks_have_no_rows(self):
        cell = ("exclude_empty", 0)
        data = record({"setup": 10}, {"setup": 10})
        out = m.assemble({cell}, {cell: data[0]}, {},
                         task=m.TASKS["task30"])
        self.assertNotIn("rows", out)
        self.assertNotIn("infeasible", out)
        self.assertNotIn("rows", m.assemble({("frag_create", 0)}, {
            ("frag_create", 0): data[0]}, {}))

    def test_the_results_name_the_rows_and_the_cells_not_run(self):
        out = m.assemble(*grid_of(TASK31), task=TASK31)
        text = m.results_markdown(out, "TASK31")
        self.assertTrue(text.startswith("# TASK31 allocation matrix"))
        self.assertIn("pass x245", text)
        self.assertIn("33 cells infeasible and not run", text)
        plain = m.results_markdown(m.assemble(
            {("exclude_empty", 0)}, {("exclude_empty", 0): record(
                {"setup": 10}, {"setup": 10})[0]}, {},
            task=m.TASKS["task30"]), "TASK30")
        self.assertNotIn("infeasible", plain)


class Dependencies(unittest.TestCase):
    """The client family's shared closure in the header and the receipts."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.sb = tb.Sandbox(Path(self.tmp.name) / "sb", pairs=2)

    def products(self, text="x"):
        out = {}
        for side, directory in self.sb.private.items():
            (directory / "numTheory.sml").write_text(text)
            out[side] = {"numTheory.sml": tb.seal(
                directory / "numTheory.sml")}
        return out

    def with_file(self, side):
        """A receipt that loads numTheory.sml from the private directory."""
        raw = str(self.sb.private[side] / "numTheory.sml")

        def mutate(events):
            first = next(i for i, e in enumerate(events) if e[0] == "use")
            events[first:first] = [["use", raw], ["used", raw]]
            last = max(i for i, e in enumerate(events) if e[0] == "loaded")
            events.insert(last + 1, ["loaded", raw])
        receipt = self.sb.receipt("candidate", side, 0, 0, mutate=mutate)
        receipt["paths"][raw] = dict(
            physical=raw, **tb.seal(Path(raw)), related_products={},
            origin="x")
        return receipt, raw

    def test_the_digest_binding_and_resume_know_the_dependencies(self):
        header = self.sb.header()
        base = m.grid_digest(header)
        header["dependencies"] = self.products()
        self.assertNotEqual(m.grid_digest(header), base)
        self.assertEqual(m.changed_settings(self.sb.header(), header),
                         ["dependencies"])
        self.assertEqual(m.changed_settings(header, header), [])
        bound = m.binding(header, tb.CASE, tb.SIZE)
        self.assertEqual(bound["dependencies"], header["dependencies"])
        self.assertNotIn("dependencies", m.binding(self.sb.header(),
                                                   tb.CASE, tb.SIZE))
        self.assertNotIn("dependencies", m.GRID_KEYS)

    def test_the_header_of_a_client_grid_holds_them_and_others_do_not(self):
        for task, expected in (("task30", False), ("task31", True)):
            with self.subTest(task):
                made = self.sb.real_grid()
                made.task = m.task_named(task)
                made.dependencies = self.products() if expected else None
                with made.make():
                    header = made.make_header(
                        tb.CAND_PIN, self.sb.header()["toolchain_products"])
                self.assertEqual("dependencies" in header, expected)

    def test_a_receipt_may_load_a_file_the_closure_installed(self):
        products = self.products()
        header = self.sb.header(dependencies=products)
        receipt, raw = self.with_file("baseline")
        meta = dict(m.binding(header, tb.CASE, tb.SIZE), schema=m.SCHEMA,
                    rejected=None)
        self.assertIn(raw, receipt["paths"])
        m.check_receipt(receipt, meta, "candidate")

    def test_a_loaded_file_of_another_content_or_unknown_is_refused(self):
        products = self.products()
        receipt, raw = self.with_file("baseline")
        for label, header in (
                ("no closure", self.sb.header()),
                ("another content", self.sb.header(dependencies={
                    s: {"numTheory.sml": dict(sha256="0" * 64, bytes=1)}
                    for s in m.SIDES})),
                ("another side", self.sb.header(dependencies={
                    s: {} if s == "baseline" else v
                    for s, v in products.items()}))):
            with self.subTest(label):
                meta = dict(m.binding(header, tb.CASE, tb.SIZE),
                            schema=m.SCHEMA, rejected=None)
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "wrong selected source"):
                    m.check_receipt(receipt, meta, "candidate")

    def test_the_products_of_an_installation_are_listed_by_name(self):
        installed = dict(products={
            ".hol/objs/numTheory.sml": dict(role="r", source="s",
                                            sha256="1" * 64, bytes=3),
            "Holmakefile": dict(sha256="2" * 64, bytes=4),
            "arithmeticTheory.uo": dict(sha256="3" * 64, bytes=5)})
        self.assertEqual(m.dependency_products(installed), {
            "numTheory.sml": dict(sha256="1" * 64, bytes=3),
            "arithmeticTheory.uo": dict(sha256="3" * 64, bytes=5)})
        installed["products"]["x/numTheory.sml"] = installed["products"][
            "Holmakefile"]
        with self.assertRaisesRegex(sc.InvalidAllocation, "ambiguous"):
            m.dependency_products(installed)


class Installation(unittest.TestCase):
    """Grid.install_private, probe_dependencies and make_job for a client
    task, with the shared closure stubbed."""
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
        grid = m.Grid.__new__(m.Grid)
        grid.task = TASK31
        grid.scratch, grid.hol = root / "scratch", self.hol
        grid.scratch.mkdir()
        grid.revisions = dict(self.REVS)
        grid.sources = {side: m.source_map([self.item]) for side in m.SIDES}
        grid.tools = {}
        self.grid, self.calls = grid, []

        def checkout(side, directory):
            directory.mkdir()
            (directory / "Foo.sml").write_text("val x = 1\n")
            return self.REVS[side], [self.item]

        def run(command, cwd):
            directory = Path(command[command.index("-C") + 1])
            (directory / "paired.exe").write_text(self.launcher)
        grid.checkout, grid.run = checkout, run
        self.content = {"n": "1"}

        def install(repo, directory, names):
            self.calls.append((repo, directory.name, sorted(names)))
            theory = directory / ".hol/objs"
            theory.mkdir(parents=True)
            data = self.content["n"].encode()
            (theory / "numTheory.sml").write_bytes(data)
            seal = a.seal(theory / "numTheory.sml")
            return dict(inputs={str(self.hol / "sigobj/x.uo"): dict(
                sha256="4" * 64, bytes=1)},
                products={".hol/objs/numTheory.sml": dict(
                    role="shared-dependency", source="s", **seal),
                    "Holmakefile": dict(sha256="5" * 64, bytes=2)})
        patcher = mock.patch.object(m.deps, "install", install)
        patcher.start()
        self.addCleanup(patcher.stop)

    def probed(self):
        for side in m.SIDES:
            self.grid.checkout(side, self.grid.scratch / ("probe-" + side))
        self.grid.dependencies = self.grid.probe_dependencies()
        return self.grid.dependencies

    def test_the_family_files_are_installed_with_the_closure(self):
        directory = self.grid.scratch / "d"
        self.grid.checkout("baseline", directory)
        found = self.grid.install_private(directory, [self.item])
        self.assertEqual(
            (directory / "Performance.sml").read_bytes(),
            (HERE / "ClientAllocation.sml").read_bytes())
        self.assertEqual((directory / "MatrixSupport.sml").read_bytes(),
                         (HERE / "MatrixSupport.sml").read_bytes())
        self.assertFalse((directory / "MatrixAllocation.sml").exists())
        self.assertIn("paired.exe: Performance.uo",
                      (directory / "Holmakefile").read_text())
        self.assertEqual(self.calls, [(self.hol, "d", ["Foo"])])
        self.assertIn(".hol/objs/numTheory.sml", found["products"])

    def test_a_matrix_task_installs_no_closure(self):
        self.grid.task = m.TASKS["task30"]
        directory = self.grid.scratch / "d"
        self.grid.checkout("baseline", directory)
        self.assertIsNone(self.grid.install_private(directory, [self.item]))
        self.assertEqual(self.calls, [])
        self.assertEqual((directory / "Performance.sml").read_bytes(),
                         (HERE / "MatrixAllocation.sml").read_bytes())
        self.assertIsNone(self.grid.probe_dependencies())

    def test_the_probe_lists_the_products_of_each_side_and_seals_inputs(
            self):
        found = self.probed()
        self.assertEqual(sorted(found), sorted(m.SIDES))
        for side in m.SIDES:
            self.assertEqual(list(found[side]), ["numTheory.sml"])
        self.assertEqual(self.grid.tools, {
            str(self.hol / "sigobj/x.uo"): dict(sha256="4" * 64, bytes=1)})
        self.assertEqual(sorted(c[1] for c in self.calls),
                         sorted("probe-" + s for s in m.SIDES))

    def test_a_control_that_differs_from_the_baseline_is_refused(self):
        original = m.dependency_products

        def other(installed):
            found = original(installed)
            self.content["n"] = "2"
            return found
        for side in m.SIDES:
            self.grid.checkout(side, self.grid.scratch / ("probe-" + side))
        with mock.patch.object(m, "dependency_products", other):
            with self.assertRaisesRegex(sc.InvalidAllocation,
                                        "control dependencies"):
                self.grid.probe_dependencies()

    def test_a_job_installs_the_closure_and_checks_it_against_the_grid(self):
        self.probed()
        job = self.grid.make_job(0)
        for side, directory in job.dirs.items():
            self.assertTrue((directory / ".hol/objs/numTheory.sml").is_file())
            self.assertIn("numTheory.sml", {
                Path(p).name for p in job.sources})
        self.assertEqual(job.names, {"Foo"})

    def test_a_closure_that_changed_since_the_probe_is_refused(self):
        self.probed()
        self.content["n"] = "changed"
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "shared closure differs"):
            self.grid.make_job(0)

    def test_a_shared_input_that_changed_is_refused(self):
        self.probed()
        self.grid.tools[str(self.hol / "sigobj/x.uo")] = dict(
            sha256="9" * 64, bytes=1)
        with self.assertRaisesRegex(sc.InvalidAllocation,
                                    "shared closure differs"):
            self.grid.make_job(0)


if __name__ == "__main__":
    unittest.main()
