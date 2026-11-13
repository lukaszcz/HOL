#!/usr/bin/env python3
"""Allocation matrix task selection: TASK29B by default, TASK30 by name.

The same synthetic fixtures as test_allocation_matrix.py and
test_allocation_grid.py; no runtime, toolchain or committed receipt.
"""
import argparse
import contextlib
import io
import json
from pathlib import Path
import re
import tempfile
import unittest
from unittest import mock

import acceptance as a
import allocation_matrix as m
import allocation_schema as sc
import allocation_testbed as tb
import matrix_schema as ms
import task29_gate as gate
import task30_cases as cases
import test_allocation_grid as grid_tests

TASK30 = m.TASKS["task30"]


class Selection(unittest.TestCase):
    def test_the_default_is_task29b_and_unchanged(self):
        self.assertEqual(m.DEFAULT_TASK, "task29b")
        self.assertEqual(m.keys(), m.keys(m.TASKS["task29b"]))
        self.assertEqual(len(m.keys()), 162)
        self.assertEqual(m.TASKS["task29b"].cases, tuple(gate.CASES))
        self.assertEqual(m.TASKS["task29b"].iterations, m.ITERATIONS)

    def test_task30_is_every_task30_case(self):
        self.assertEqual(len(cases.CASES), 24)
        self.assertEqual(TASK30.cases, cases.CASES)
        self.assertEqual(len(m.keys(TASK30)), 144)
        self.assertFalse(set(TASK30.cases) & set(gate.CASES))
        self.assertFalse(hasattr(TASK30, "excluded"))
        self.assertFalse(hasattr(cases, "ALLOCATION_EXCLUDED"))

    def test_the_cases_are_the_matrix_exclusion_and_history_cases(self):
        matrix = [c for c in ms.EXPECTED_CASES
                  if c.startswith(("exclude_", "history_"))]
        self.assertEqual(sorted(cases.CASES), sorted(matrix))
        text = (m.HERE / "MatrixSupport.sml").read_text()
        listed = re.search(r"val cases =\s*\[(.*?)\]", text, re.S)
        found = set(re.findall(r'"(exclude_\w+|history_\w+)"',
                               listed.group(1)))
        self.assertLessEqual(set(cases.CASES), found)
        for case in cases.CASES:
            self.assertEqual(ms.EXPECTED_CASES[case]["sizes"], "rules")

    def test_sizes_are_the_gate_sizes(self):
        for case in cases.CASES:
            sizes = ms.SIZE_SETS[ms.EXPECTED_CASES[case]["sizes"]]
            self.assertEqual(tuple(sizes), m.SIZES, case)

    def test_unknown_tasks_are_refused(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "unknown task"):
            m.task_named("task99")
        with self.assertRaisesRegex(sc.InvalidAllocation, "unknown task"):
            m.task_of(dict(task="nope"))
        self.assertIs(m.task_of({}), m.TASKS["task29b"])
        self.assertIs(m.task_of(dict(task="task30")), TASK30)

    def test_the_theory_change_case_is_gated_at_every_size(self):
        found = {m.name_of(*k) for k in m.keys(TASK30)}
        for size in m.SIZES:
            self.assertIn("history_theory_change-%d" % size, found)


class Counts(unittest.TestCase):
    def test_the_committed_counts_follow_the_fixed_rule(self):
        counts = m.load_iterations(task=TASK30)
        self.assertEqual(len(counts["steady"]), 144)
        self.assertEqual(counts["repeats"], 4)
        base = a.load(m.ITERATIONS)
        self.assertEqual((counts["schema"], counts["rule"]),
                         (base["schema"], base["rule"]))
        for key, value in counts["steady"].items():
            size = int(key.rsplit("-", 1)[1])
            self.assertEqual(value, 32 if size <= 100 else
                             16 if size == 1000 else 8, key)

    def test_the_rule_is_the_one_of_the_other_counts(self):
        base = a.load(m.ITERATIONS)
        other = a.load(TASK30.iterations)
        self.assertEqual((base["rule"], base["repeats"]),
                         (other["rule"], other["repeats"]))
        for counts in (base, other):
            for key, value in counts["steady"].items():
                size = int(key.rsplit("-", 1)[1])
                self.assertEqual(value, 32 if size <= 100 else
                                 16 if size == 1000 else 8, key)
        self.assertFalse(set(base["steady"]) & set(other["steady"]))

    def test_counts_of_another_task_are_refused(self):
        with self.assertRaisesRegex(sc.InvalidAllocation, "incomplete"):
            m.load_iterations(TASK30.iterations)
        with self.assertRaisesRegex(sc.InvalidAllocation, "incomplete"):
            m.load_iterations(m.ITERATIONS, TASK30)

    def test_a_missing_or_extra_cell_is_refused(self):
        good = a.load(TASK30.iterations)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "c.json"
            for steady in (
                    {k: v for k, v in good["steady"].items()
                     if k != "history_makers-10"},
                    dict(good["steady"], **{"frag_create-0": 32})):
                path.write_text(json.dumps(dict(good, steady=steady)))
                with self.assertRaisesRegex(sc.InvalidAllocation,
                                            "incomplete"):
                    m.load_iterations(path, TASK30)


class Binding(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.sb = tb.Sandbox(Path(self.tmp.name) / "sb", pairs=2)

    def test_the_task_is_part_of_the_grid_digest_only_when_named(self):
        header = self.sb.header()
        base = m.grid_digest(header)
        self.assertEqual(m.grid_digest(dict(header, task="task29b")), base)
        other = m.grid_digest(dict(header, task="task30"))
        self.assertNotEqual(other, base)
        self.assertEqual(m.grid_digest(dict(header, task="task30")), other)

    def test_a_resume_under_another_task_is_a_different_grid(self):
        header = self.sb.header()
        self.assertEqual(m.changed_settings(header, header), [])
        self.assertEqual(m.changed_settings(header, dict(
            header, task="task30")), ["task"])
        self.assertEqual(m.changed_settings(
            dict(header, task="task30"), header), ["task"])
        self.assertEqual(m.changed_settings(
            dict(header, task="task29b"), header), [])

    def test_the_header_names_a_non_default_task_only(self):
        for task, expected in (("task29b", {}), ("task30", dict(
                task="task30"))):
            with self.subTest(task):
                made = self.sb.real_grid()
                made.task = m.task_named(task)
                with made.make():
                    header = made.make_header(
                        tb.CAND_PIN, self.sb.header()["toolchain_products"])
                self.assertEqual({k: v for k, v in header.items()
                                  if k == "task"}, expected)

    def test_the_bound_counts_are_those_of_the_selected_task(self):
        sizes = m.load_iterations(task=TASK30)["steady"]
        header = dict(self.sb.header(), task="task30",
                      iterations=m.load_iterations(task=TASK30))
        found = m.binding(header, "exclude_empty", 10)
        self.assertEqual(found["steady"], sizes["exclude_empty-10"])
        self.assertEqual(found["grid"], m.grid_digest(header))

    def test_the_grid_takes_its_task_from_the_arguments(self):
        repo = a.HERE.parents[3]
        for name in ("task29b", "task30"):
            args = argparse.Namespace(pairs=2, repo=repo, task=name)
            self.assertEqual(m.Grid(args).task.name, name)
        args = argparse.Namespace(pairs=2, repo=repo)
        self.assertEqual(m.Grid(args).task.name, "task29b")

    def test_the_prepared_grid_binds_the_harness_of_its_task(self):
        repo = a.HERE.parents[3]
        for name in ("task29b", "task30"):
            bound = []
            with mock.patch.object(
                    m, "harness_binding",
                    lambda root, candidate, inputs, fixtures:
                    bound.append((candidate, sorted(
                        p.name for p in inputs))) or dict(bound=name)):
                grid = m.Grid(argparse.Namespace(
                    pairs=2, repo=repo, task=name))
                binding, inputs, fixtures = grid.bind_harness("c" * 40)
                self.assertEqual(binding, dict(bound=name))
                self.assertEqual(
                    (inputs, fixtures),
                    m.harness_files(m.TASKS[name]))
            (candidate, inputs), = bound
            self.assertEqual(candidate, "c" * 40)
            ours = m.TASKS[name].iterations.name
            self.assertIn(ours, inputs)
            for other in m.TASKS.values():
                if other.iterations.name != ours:
                    self.assertNotIn(other.iterations.name, inputs)

    def test_the_digest_of_a_task29b_header_is_that_of_294bb61c3(self):
        # Computed with the grid_digest of 294bb61c3 on this header.
        self.assertEqual(m.GRID_KEYS, (
            "schema", "baseline", "candidate", "pairs", "runtime", "shim",
            "repo", "toolchain_head", "toolchain_products", "tools",
            "inputs", "controls", "sources", "revisions", "fixtures",
            "word_bytes", "canary", "iterations", "environment", "boundary",
            "harness"))
        header = {k: "v-" + k for k in m.GRID_KEYS}
        header.update(pairs=10, iterations={"steady": {"a-0": 32}})
        golden = ("e5fa929004e714b8425ef7bf51f44a98"
                  "f750b3bbfbfcb4eb97f3c22da9ac3027")
        self.assertEqual(m.grid_digest(header), golden)
        self.assertEqual(m.grid_digest(dict(header, task="task29b")), golden)

    def test_assembly_takes_the_cases_of_the_task(self):
        cell = {("exclude_empty", 0)}
        name = m.name_of("exclude_empty", 0)
        self.assertEqual(m.assemble(cell, {}, {}, task=TASK30)[
            "unresolved"], [name])
        self.assertEqual(m.assemble(cell, {}, {})["unresolved"], [])

    def test_the_harness_binds_the_selected_counts_and_the_case_list(self):
        def names(task):
            inputs, _ = m.harness_files(task)
            return {p.name for p in inputs}
        self.assertIn("allocation_iterations.json",
                      names(m.TASKS["task29b"]))
        self.assertNotIn("allocation_iterations_task30.json",
                         names(m.TASKS["task29b"]))
        self.assertIn("allocation_iterations_task30.json", names(TASK30))
        self.assertNotIn("allocation_iterations.json", names(TASK30))
        for task in m.TASKS.values():
            self.assertIn("task30_cases.py", names(task))
        self.assertEqual({p.name for p in m.harness_files()[0]},
                         names(m.TASKS["task29b"]))


class Run(grid_tests.Bed):
    """A stub run of TASK30 cells: header, inventory, replay and labels."""

    def patched30(self):
        stub, log = grid_tests.make_stub(self.sb)

        class Task(stub):
            def __init__(self, args):
                super().__init__(args)
                task = getattr(args, "task", m.DEFAULT_TASK)
                if task != m.DEFAULT_TASK:
                    self.header = dict(self.header, task=task)
        patcher = mock.patch.object(m, "Grid", Task)
        patcher.start()
        self.addCleanup(patcher.stop)
        return log

    def test_a_task30_cell_runs_replays_and_is_labelled(self):
        self.patched30()
        code = self.quiet(m.run, grid_tests.arguments(
            self.out, ["exclude_empty-0", "history_makers-10"],
            task="task30"))
        self.assertEqual(code, 2)
        inventory = a.load(self.out / "inventory.json")
        self.assertEqual(inventory["task"], "task30")
        self.assertEqual(sorted(r["case"] for r in inventory["runs"]),
                         ["exclude_empty", "history_makers"])
        steady = m.load_iterations(task=TASK30)["steady"]
        self.assertEqual({r["case"]: r["steady"]
                          for r in inventory["runs"]},
                         {"exclude_empty": steady["exclude_empty-0"],
                          "history_makers": steady["history_makers-10"]})
        self.assertTrue((self.out / "RESULTS-partial.md").read_text(
            ).startswith("# TASK30 allocation matrix"))
        args = type("Args", (), {"output": self.out})
        self.assertEqual(self.quiet(m.replay, args), 2)

    def test_the_stub_runs_theory_change_cells_at_the_table_counts(self):
        # The stub runner only shows that the cells are in the table and
        # take its steady counts; the case's own code is checked by
        # TheoryChange from the fixture text, and runs in HOL only.
        self.patched30()
        code = self.quiet(m.run, grid_tests.arguments(
            self.out, ["history_theory_change-0",
                       "history_theory_change-10000"], task="task30"))
        self.assertEqual(code, 2)
        inventory = a.load(self.out / "inventory.json")
        self.assertEqual(sorted((r["case"], r["size"])
                                for r in inventory["runs"]),
                         [("history_theory_change", 0),
                          ("history_theory_change", 10000)])
        steady = m.load_iterations(task=TASK30)["steady"]
        self.assertEqual({r["size"]: r["steady"] for r in inventory["runs"]},
                         {0: steady["history_theory_change-0"],
                          10000: steady["history_theory_change-10000"]})

    def test_the_theory_change_case_is_not_a_task29b_cell(self):
        self.patched30()
        with self.assertRaisesRegex(sc.InvalidAllocation, "unknown"):
            self.quiet(m.run, grid_tests.arguments(
                self.out, ["history_theory_change-0"]))

    def test_task29b_cells_are_not_task30_cells(self):
        self.patched30()
        with self.assertRaisesRegex(sc.InvalidAllocation, "unknown"):
            self.quiet(m.run, grid_tests.arguments(
                self.out, ["frag_create-0"], task="task30"))
        with self.assertRaisesRegex(sc.InvalidAllocation, "unknown"):
            self.quiet(m.run, grid_tests.arguments(
                self.root / "other", ["exclude_empty-0"]))

    def test_resume_under_another_task_is_refused(self):
        self.patched30()
        self.quiet(m.run, grid_tests.arguments(
            self.out, ["exclude_empty-0"], task="task30"))
        with self.assertRaisesRegex(
                sc.InvalidAllocation, "resume with different settings.*task"):
            self.quiet(m.run, grid_tests.arguments(
                self.out, ["frag_create-0"], resume=True))

    def test_the_task_option_is_on_the_command_line(self):
        with mock.patch.object(m, "run", lambda args: args.task):
            argv = ["run", "--output", "o", "--candidate", "c" * 40,
                    "--toolchain", "t", "--controls-receipt", "r"]
            self.assertEqual(m.main(argv), "task29b")
            self.assertEqual(m.main(argv + ["--task", "task30"]), "task30")
            with contextlib.redirect_stderr(io.StringIO()), \
                    self.assertRaises(SystemExit):
                m.main(argv + ["--task", "task99"])


class Fixture(unittest.TestCase):
    """The allocation fixture brackets any MatrixSupport case, whole."""

    @classmethod
    def setUpClass(cls):
        cls.text = (m.HERE / "MatrixAllocation.sml").read_text()

    def test_every_phase_of_a_case_is_inside_a_bracket(self):
        self.assertIn('bracket "setup" (fn () => cell := SOME '
                      '(workload label size))', self.text)
        self.assertIn('batch "operation_first" 1 run', self.text)
        self.assertIn('batch "operation_steady" steady (fn () => '
                      'repeat steady run)', self.text)
        self.assertIn('bracket "apply" verify', self.text)

    def test_callbacks_run_outside_the_brackets(self):
        start = self.text.index("fun batch name count work")
        end = self.text.index("val _ = batch \"operation_first\"")
        body = self.text[start:end]
        self.assertLess(body.index("beforeBatch ()"),
                        body.index("bracket name work"))
        self.assertLess(body.index("bracket name work"),
                        body.index("afterBatch count"))

    def test_every_phase_is_gated(self):
        import allocation_analysis as an
        self.assertEqual(set(an.GATED), {
            "setup", "operation_first", "operation_steady", "apply"})

    def test_the_case_label_is_not_restricted_to_task29b(self):
        self.assertIn("Lib.mem label cases", self.text)
        support = (m.HERE / "MatrixSupport.sml").read_text()
        for case in cases.CASES:
            self.assertIn('"%s"' % case, support)


def code(text):
    """SML source without its comments."""
    return re.sub(r"\(\*.*?\*\)", "", text, flags=re.S)


class StructureFixture(unittest.TestCase):
    """The work phase is untimed, after the last bracket, and does not
    touch what the brackets measure; the hook of the result fingerprint is
    set when a workload is built."""

    @classmethod
    def setUpClass(cls):
        cls.allocation = code((m.HERE / "MatrixAllocation.sml").read_text())
        cls.support = code((m.HERE / "MatrixSupport.sml").read_text())
        cls.timing = code((m.HERE / "MatrixPerformance.sml").read_text())

    def test_the_work_phase_follows_the_last_bracket(self):
        text = self.allocation
        self.assertEqual(text.count("workPhase"), 1)
        self.assertEqual(text.count("bracket "), len(re.findall(
            r"\bbracket\b", text)))
        start = text.index("val work = workPhase (valOf (!cell))")
        self.assertLess(text.index('bracket "apply" verify'), start)
        self.assertLess(text.index("val _ = experiment ()"), start)
        self.assertLess(start, text.index("fun emitBracket"))
        self.assertNotIn("workPhase", text[:text.index("fun experiment")])

    def test_the_records_follow_the_foreign_thread_record(self):
        text = self.allocation
        foreign = text.index('Paired.observe "alloc.foreign"')
        emit = text.index("List.app (fn (key, value) => "
                          "Paired.observe key value) work")
        check = text.index('Paired.check "allocation brackets" true')
        self.assertLess(foreign, emit)
        self.assertLess(emit, check)

    def test_the_phase_names_its_records_as_the_schema_does(self):
        start = self.support.index("fun workPhase")
        body = self.support[start:self.support.index("fun constant", start)]
        self.assertEqual(tuple(re.findall(r'\("([\w.]+)",', body)),
                         sc.WORK_EVENTS)
        # the use runs under the same counters as the operations
        self.assertIn("val use = counted (!useResult)", body)
        self.assertIn("val first = measureOnce w", body)
        self.assertLess(body.index("val second"), body.index("val use"))
        self.assertLess(body.index("val digest"), body.index("val use"))

    def test_the_listener_counts_and_never_forces_a_lazy_text(self):
        start = self.support.index("fun listen (level,a)")
        body = self.support[start:self.support.index("val maker0", start)]
        self.assertIn("actionIndex a", body)
        for token in ("LZ_TEXT", "print", "say", "term_to_string", "()"):
            self.assertNotIn(token, body)
        # the one payload it reads is the string of a TEXT
        self.assertEqual(re.findall(r"Trace\.\w+ \w+", body),
                         ["Trace.TEXT s"])
        self.assertIn("Trace.TEXT s => escapeText s", body)
        sig = (m.HERE.parents[1] / "src" / "Trace.sig").read_text()
        self.assertRegex(sig, r"\bTEXT\s+of string\b")
        self.assertRegex(sig, r"LZ_TEXT\s+of unit -> string")
        index = self.support.index("fun actionIndex a")
        self.assertIn("Trace.LZ_TEXT _ => 1",
                      self.support[index:self.support.index("val textIndex")])

    def test_levels_are_exact_and_keys_ordered_by_the_schema(self):
        start = self.support.index("fun counted")
        counted = self.support[start:self.support.index("fun measureOnce")]
        for token in ("Int.min", "Int.max", "Array"):
            self.assertNotIn(token, counted)
        self.assertIn("Int.compare (l1,l2)", self.support)
        self.assertIn("val textIndex = 10", self.support)
        self.assertEqual(sc.TRACE_ACTIONS.index("TEXT"), 10)

    def test_the_listener_is_removed_and_counting_stopped_on_any_exit(self):
        self.assertIn("Portable.finally cleanup body ()", self.support)
        start = self.support.index("fun cleanup () =")
        cleanup = self.support[start:self.support.index("val _ =", start)]
        self.assertIn('Listener.remove_listener Trace.trace_hook '
                      '"matrix_work"', cleanup)
        self.assertIn("Count.counting_thms false", cleanup)
        self.assertIn('Listener.add_listener Trace.trace_hook '
                      '("matrix_work",listen)', self.support)

    ALLOWED_HOOK_LINES = (
        r"fun retaining text use = \(fingerprint := text; "
        r"useResult := use\)",
        r"val _ = \(ruleList := rs; fingerprint := missingFingerprint;",
        r"useResult := noUse; localCalls := noCalls\)",
        r"val _ = localCalls := \(fn \(\) => !calls1 \+ !calls2\)")

    @classmethod
    def stray_hook_assignments(cls, text):
        """The lines that assign a hook and are none of the exact allowed
        lines (the hooks are set by the workload constructors only)."""
        return [l for l in text.splitlines()
                if re.search(r"\b(fingerprint|useResult|localCalls|"
                             r"ruleList) :=", l)
                and not any(re.fullmatch(r"\s*" + a + r"\s*", l)
                            for a in cls.ALLOWED_HOOK_LINES)]

    def test_a_use_of_a_simpset_applies_its_dprocs_and_counts_them(self):
        text = self.support
        self.assertIn("fun useSS ss = (lookups ss ignore; useDprocs ss)",
                      text)
        use = text[text.index("fun useDprocs"):text.index("fun useSS")]
        # each dproc itself, on a sample of left sides
        self.assertIn("Traverse.dest_reducer d", use)
        self.assertIn("List.app (apply tm) dprocs", use)
        self.assertIn("Lib.mk_set [0,n div 2,n-1]", use)
        # the netconv of the digest and of the net lookups has none
        net = text[text.index("fun netconv"):
                   text.index("val missingFingerprint")]
        self.assertIn("dprocs=[]", net)
        # the fixture's dproc counts its own applications, and the counter
        # is read by the work records beside the maker and collector's
        shared = text[text.index("fun dprocApply"):
                      text.index("fun reducer name")]
        self.assertIn("dprocCalls := !dprocCalls + 1", shared)
        self.assertIn("raise Conv.UNCHANGED", shared)
        # one shared closure: no per-reducer closure over the counter, which
        # would grow the setup words with the number of dprocs
        reducer = text[text.index("fun reducer name"):
                       text.index("fun setup")]
        self.assertIn("apply=dprocApply", reducer)
        self.assertNotIn("dprocCalls", reducer)
        self.assertIn('";dproc=" ^ Int.toString (!dprocCalls - dproc0)', text)

    def test_the_digest_is_read_before_the_use(self):
        start = self.support.index("fun workPhase")
        phase = self.support[start:self.support.index("fun constant")]
        self.assertLess(phase.index("val digest = (!fingerprint) ()"),
                        phase.index("val use = counted (!useResult)"))

    def test_a_stray_hook_assignment_is_found(self):
        for bad in ("val _ = ruleList := []",
                    "      fn () => (useResult := noUse; run ())",
                    "val _ = (ruleList := rs; fingerprint := noUse;"):
            with self.subTest(bad):
                self.assertEqual(self.stray_hook_assignments(
                    self.support + "\n" + bad + "\n"), [bad])

    def test_the_hooks_are_assigned_only_where_a_workload_is_built(self):
        text = self.support
        calls = [u for u in re.findall(r"[^\n]*\bretaining\b[^\n]*", text)
                 if "fun retaining" not in u]
        # sswork, thwork, convwork, fragwork, markerTactic, the theory
        # change and the storage graph, each at construction time
        self.assertEqual(len(calls), 7)
        for u in calls:
            self.assertTrue(u.lstrip().startswith("val _ = retaining"), u)
            self.assertNotIn("fn () => slot :=", u)
        # the hooks themselves are assigned nowhere else
        self.assertEqual(self.stray_hook_assignments(text), [])
        self.assertIn("val fingerprint : (unit -> string) ref = "
                      "ref missingFingerprint", text)
        # a workload built after another never reads its hooks
        self.assertIn("val _ = (ruleList := rs; fingerprint := "
                      "missingFingerprint;\n             useResult := noUse; "
                      "localCalls := noCalls)", text)

    def test_the_makers_of_history_makers_count_in_the_work_record(self):
        start = self.support.index('"history_makers" =>')
        end = self.support.index('"history_theory_change" =>', start)
        case = self.support[start:end]
        self.assertIn("val _ = localCalls := (fn () => !calls1 + !calls2)",
                      case)
        # the maker bodies, which run in the timed closure, are untouched
        self.assertIn("fun firstMaker rw = (calls1 := !calls1 + 1; [rw])",
                      case)
        self.assertIn("fun laterMaker rw = (calls2 := !calls2 + 1; [rw])",
                      case)
        self.assertNotIn("makerCalls", case)
        count = self.support.index("val maker0 = ")
        self.assertIn("(!localCalls) ()", self.support[count:count + 200])

    def test_setup_allocates_no_copy_of_the_rules(self):
        self.assertNotIn("Vector.fromList", self.support)
        self.assertIn("ruleList := rs", self.support)
        # the terms of the conversion are made when the work phase asks
        self.assertIn("(fn () => miss :: map", self.support)

    def test_the_use_of_a_simpset_is_the_traversal_of_all_the_rules(self):
        start = self.support.index("fun lookups")
        body = self.support[start:self.support.index("fun useDprocs")]
        self.assertIn("netconv ss", body)
        self.assertIn("(!ruleList)", body)
        # the same traversal gives the REFL set of the fingerprint
        self.assertIn("val _ = lookups ss note", self.support)
        self.assertIn("fun useSS ss = (lookups ss ignore; useDprocs ss)",
                      self.support)
        # a built simpset, a fragment, the deletion and the history cases
        # all use their retained simpset; a bare theorem has no use
        self.assertIn("(fn () => useSS (!slot))", self.support)
        self.assertIn("(fn () => useSS (empty_ss ++ !slot))", self.support)
        self.assertIn("val _ = retaining (fn () => thmText (!slot)) noUse",
                      self.support)

    def test_the_fingerprints_read_the_retained_result(self):
        # a fragment: the structural key of every rule it holds, not its
        # agreement with what verify already required
        start = self.support.index("fun fragText")
        body = self.support[start:self.support.index("fun fragworkWith")]
        self.assertIn("map thmKey actual", body)
        self.assertNotIn("thmText", body)
        self.assertIn("hashText", body)
        self.assertNotIn("expected", body)
        # types are shown in goals as in theorems
        self.assertIn("Globals.show_types,true", self.support)
        start = self.support.index("fun goalText")
        self.assertIn("termText", self.support[start:start + 120])
        # the theory change keeps the function that raised the error
        self.assertIn("Feedback.top_function_of e", self.support)
        # the theorems of the lookups that are not REFL are in the digest
        start = self.support.index("fun ssText")
        body = self.support[start:self.support.index("type workload")]
        self.assertIn("thmKey th :: !others", body)
        self.assertNotIn("thmText", body)

    def test_the_hashed_rule_lists_use_the_structural_key(self):
        # printing n rules over n constants costs n^2 (PROTOCOL.md); the key
        # is built from the term and type structure, never the printer
        start = self.support.index("fun keyName")
        end = self.support.index("fun hashText")
        key = self.support[start:end]
        # every name is length-prefixed, so the key decodes uniquely
        self.assertIn('fun keyName s = Int.toString (size s) ^ ":" ^ s', key)
        # each constructor of a term and of a type, with its tag
        for token in ('"\'" :: keyName (dest_vartype ty)',
                      '"V" :: keyName s :: tyKey ty acc',
                      '"A" :: tmKey f (tmKey x acc)',
                      '"L" :: tmKey v (tmKey b acc)'):
            self.assertIn(token, key)
        # the theory and the name of a constant, its type, the theory and
        # the operator of a type, and its arguments
        self.assertIn("tyKey Ty acc end", key)
        self.assertIn("if shown = #Name (KernelSig.name_of_id id) then live "
                      "else retired", key)
        self.assertIn("Int.toString (length Args) ::", key)
        self.assertIn("List.foldr (fn (a,acc) => tyKey a acc) acc Args", key)
        # a constant or type operator by its display name, which keeps the
        # generation of a retired one
        self.assertIn("Term.dest_thy_constid tm", key)
        self.assertIn("val shown = Term.display_name_of_id Name", key)
        self.assertIn('idTag "C" "c" Name shown :: keyName Thy :: '
                      "keyName shown ::", key)
        self.assertIn("Type.dest_thy_typeid ty", key)
        self.assertIn("val shown = Type.display_name_of_id Tyop", key)
        self.assertIn('idTag "T" "t" Tyop shown :: keyName Thy :: '
                      "keyName shown ::", key)
        self.assertNotIn("uptodate", key)
        # the hypotheses (counted, in order) and the conclusion
        self.assertIn("Int.toString (length (hyp th))", key)
        self.assertIn("List.foldr (fn (h,acc) => tmKey h acc) "
                      '("|" :: tmKey (concl th) [])', key)
        for token in ("term_to_string", "thm_to_string", "termText",
                      "thmText", "Parse."):
            self.assertNotIn(token, key)
        # the printed forms of the other fixtures are as they were
        for text in (
                "fun termText tm = Lib.with_flag (Globals.show_types,true)\n"
                "    (fn () => printable (Parse.term_to_string tm)) ()\n",
                "fun thmText th = String.concatWith \",\" (map termText "
                "(hyp th)) ^ \" |- \" ^\n                   termText "
                "(concl th)\n",
                "fun goalText (asl,w) =\n    String.concatWith \",\" (map "
                "termText asl) ^ \" ?- \" ^ termText w\n"):
            self.assertIn(text, self.support)
        self.assertEqual(self.support.count("thmKey"), 3)

    def test_the_timing_fixture_knows_nothing_of_it(self):
        for token in ("workPhase", "fingerprint", "Listener", "Count."):
            self.assertNotIn(token, self.timing)

    def test_the_support_reads_no_clock_and_no_state_outside_its_refs(self):
        for token in ("Time.", "Timer.", "Random", "OS.Process", "getEnv"):
            self.assertNotIn(token, self.support)


class Smoke(unittest.TestCase):
    """The operator smoke runs the work phase of every case."""

    @classmethod
    def setUpClass(cls):
        import smoke_matrix
        cls.smoke = smoke_matrix

    def test_the_selftest_runs_the_phase_twice_and_prints_its_records(self):
        text = self.smoke.SELFTEST
        self.assertEqual(text.count("workPhase wl"), 2)
        self.assertIn("val wl as {run,verify,beforeBatch,afterBatch} = "
                      "workload label n", text)
        self.assertIn("@@MATRIX_WORK", text)
        # steady-state counts and the digest reproduce within the process
        self.assertIn('field "work.second" work', text)
        self.assertIn('field "work.use" again', text)
        self.assertIn('field "result.digest" again', text)

    def lines(self, sizes, labels, change=lambda rows: None):
        rows = [[c, str(n), k, v] for n in sizes for c in labels
                for k, v in zip(sc.WORK_EVENTS, (
                    "trace=2.TEXT:x=1;kernel=;maker=0;collector=0;"
                    "dproc=0",
                    "trace=;kernel=SPEC=1,total=1;maker=2;collector=0;"
                    "dproc=0",
                    "trace=4.REDUCE=3;kernel=;maker=0;collector=0;dproc=0",
                    "digest text"))]
        change(rows)
        return "\n".join("@@MATRIX_WORK\t" + "\t".join(r) for r in rows)

    def test_valid_records_are_parsed(self):
        records = self.smoke.work_records(self.lines([0, 1], ["a", "b"]),
                                          [0, 1], ["a", "b"])
        self.assertEqual(len(records), 16)
        self.assertEqual(records[0], dict(
            case="a", size=0, key="work.first",
            value="trace=2.TEXT:x=1;kernel=;maker=0;collector=0;"
                  "dproc=0"))
        self.assertEqual(records[-1]["value"], "digest text")

    def test_missing_extra_misordered_and_malformed_records_are_refused(self):
        run = lambda text: self.smoke.work_records(text, [0], ["a"])
        good = self.lines([0], ["a"])
        run(good)
        for label, text in (
                ("missing", "\n".join(good.splitlines()[:-1])),
                ("extra", good + "\n" + good.splitlines()[0]),
                ("misordered", "\n".join(reversed(good.splitlines()))),
                ("empty", ""),
                ("bad key", good.replace("work.use", "work.third")),
                ("use missing", "\n".join(
                    l for l in good.splitlines() if "work.use" not in l)),
                ("bad counts", good.replace("SPEC=1", "NOPE=1")),
                ("short", good.replace("\tdigest text", ""))):
            with self.subTest(label), self.assertRaises(
                    (ValueError, sc.InvalidAllocation)):
                run(text)


class CrossSide(unittest.TestCase):
    """The comparison of the work records of the two sides."""

    @classmethod
    def setUpClass(cls):
        import smoke_matrix
        cls.smoke = smoke_matrix

    COUNTS = "trace=4.REDUCE=3;kernel=;maker=0;collector=0;dproc=0"

    def run_of(self, selection, change=lambda rows: None, accepted=True):
        rows = [dict(case=c, size=n, key=k, value=v)
                for n in (0, 1) for c in ("a", "b")
                for k, v in zip(sc.WORK_EVENTS, (
                    self.COUNTS, self.COUNTS, self.COUNTS, "digest"))]
        change(rows)
        return dict(selection=selection, work=rows, accepted=accepted)

    def test_equal_sides_compare_equal(self):
        cross = self.smoke.compare_sides([self.run_of("baseline"),
                                          self.run_of("candidate")])
        self.assertEqual(cross, dict(compared=16, differences=[]))

    def test_a_count_difference_names_the_count(self):
        def more(rows):
            rows[2]["value"] = self.COUNTS.replace("REDUCE=3", "REDUCE=4")
        cross = self.smoke.compare_sides([self.run_of("baseline"),
                                          self.run_of("candidate", more)])
        self.assertEqual(len(cross["differences"]), 1)
        d = cross["differences"][0]
        self.assertEqual((d["case"], d["size"], d["key"]),
                         ("a", 0, "work.use"))
        self.assertEqual(d["counts"], {"trace.4.REDUCE": [3, 4]})

    def test_a_digest_difference_and_a_missing_record_differ(self):
        def change(rows):
            rows[3]["value"] = "other"
            del rows[8]
        cross = self.smoke.compare_sides([self.run_of("baseline"),
                                          self.run_of("candidate", change)])
        self.assertEqual([(d["case"], d["size"], d["key"])
                          for d in cross["differences"]],
                         [("a", 0, "result.digest"), ("a", 1, "work.first")])
        self.assertNotIn("counts", cross["differences"][0])
        self.assertIsNone(cross["differences"][1]["candidate"])

    def test_a_duplicate_record_is_refused(self):
        with self.assertRaises(ValueError):
            self.smoke.compare_sides([self.run_of("baseline"),
                                      self.run_of("baseline")])

    def test_nothing_is_compared_without_records(self):
        self.assertEqual(self.smoke.compare_sides([]),
                         dict(compared=0, differences=[]))

    def test_the_command_line_compares_a_manifest(self):
        import sys
        runs = [self.run_of("baseline"), self.run_of("candidate")]
        for change, code in ((lambda rows: None, 0),
                             (lambda rows: rows[0].update(value="trace=;"
                              "kernel=;maker=1;collector=0;dproc=0"), 1)):
            runs[1] = self.run_of("candidate", change)
            with tempfile.TemporaryDirectory() as tmp:
                path = Path(tmp) / "manifest.json"
                path.write_text(json.dumps(dict(runs=runs)))
                argv = ["smoke_matrix.py", "--compare", str(path)]
                out = io.StringIO()
                with mock.patch.object(sys, "argv", argv), \
                        contextlib.redirect_stdout(out):
                    self.assertEqual(self.smoke.main(), code)
                self.assertIn("16 compared", out.getvalue())
                self.assertEqual("DIFFERS" in out.getvalue(), bool(code))

    def test_the_summary_is_derived_from_the_manifest_alone(self):
        import sys
        runs = [self.run_of("baseline"), self.run_of("candidate")]
        manifest = dict(runs=runs, head="abc", selections={
            "baseline": dict(revision="b"), "candidate": dict(revision="c")},
            inputs={"x": 1})
        summary = self.smoke.summarise(manifest)
        self.assertEqual(summary["head"], "abc")
        self.assertEqual(summary["selections"], dict(baseline="b",
                                                     candidate="c"))
        self.assertEqual(summary["cross_side"],
                         dict(compared=16, differences=[]))
        self.assertEqual(summary["rows"]["baseline"]["a:0"]["work.use"],
                         dict(events=3, inferences=0, maker=0, collector=0,
                              dproc=0))
        self.assertEqual(len(summary["rows"]["candidate"]), 4)
        self.assertEqual(len(summary["rows"]["candidate"]["a:0"]["result"
                                                               ".digest"]), 64)
        with tempfile.TemporaryDirectory() as tmp:
            path, out = Path(tmp) / "manifest.json", Path(tmp) / "s.json"
            path.write_text(json.dumps(manifest))
            argv = ["smoke_matrix.py", "--compare", str(path),
                    "--write-summary", str(out)]
            with mock.patch.object(sys, "argv", argv), \
                    contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(self.smoke.main(), 0)
            self.assertEqual(json.loads(out.read_text()), summary)

            def compare():
                argv = ["smoke_matrix.py", "--compare", str(path),
                        "--summary", str(out)]
                text = io.StringIO()
                with mock.patch.object(sys, "argv", argv), \
                        contextlib.redirect_stdout(text):
                    return self.smoke.main(), text.getvalue()
            code, text = compare()
            self.assertEqual(code, 0)
            self.assertNotIn("DIFFERS", text)
            stored = json.loads(out.read_text())
            stored["head"] = "other"
            out.write_text(json.dumps(stored))
            code, text = compare()
            self.assertEqual(code, 1)
            self.assertIn("DIFFERS summary", text)

    def test_the_run_writes_the_manifest_and_the_summary(self):
        text = Path(self.smoke.__file__).read_text()
        self.assertIn('summarypath = output.with_suffix(".summary.json")',
                      text)
        self.assertIn("json.dumps(summarise(manifest), indent=2)", text)

    def test_the_run_reports_and_exits_on_the_comparison(self):
        text = Path(self.smoke.__file__).read_text()
        self.assertIn('manifest["cross_side"] = compare_sides('
                      'manifest["runs"])', text)
        self.assertIn('not cross["differences"]', text)


class TheoryChange(unittest.TestCase):
    """history_theory_change in the allocation gate: the fixture makes no
    theory transition there, and the timing gate keeps the real one."""

    @classmethod
    def setUpClass(cls):
        cls.support = code((m.HERE / "MatrixSupport.sml").read_text())
        cls.allocation = code((m.HERE / "MatrixAllocation.sml").read_text())
        cls.timing = code((m.HERE / "MatrixPerformance.sml").read_text())
        start = cls.support.index('| "history_theory_change" =>')
        end = cls.support.index('| _ => raise Fail "unknown history case"',
                                start)
        cls.case = cls.support[start:end]

    def test_the_case_goes_through_the_hook(self):
        self.assertIn('(!theoryChange) "matrix_changed"', self.case)
        self.assertNotIn("new_theory", self.case)

    def test_the_hook_defaults_to_the_real_transition(self):
        self.assertEqual(re.findall(r"new_theory[^\n]*", self.support),
                         ["new_theory name))"])
        self.assertIn("val theoryChange = ref (fn name => ignore "
                      "(new_theory name))", self.support)

    def test_the_allocation_fixture_removes_it_before_any_bracket(self):
        replaced = self.allocation.index(
            "val _ = theoryChange := (fn _ => ())")
        self.assertLess(self.allocation.index("open HolKernel Paired "
                                              "MatrixSupport"), replaced)
        self.assertLess(replaced, self.allocation.index("fun bracket"))
        self.assertEqual(re.findall(r"new_theory[^\n]*", self.allocation),
                         ['new_theory "matrix_allocation"'])

    def test_the_timing_fixture_keeps_the_real_transition(self):
        self.assertNotIn("theoryChange", self.timing)
        self.assertEqual(re.findall(r"new_theory[^\n]*", self.timing),
                         ['new_theory "matrix_performance"'])

    def test_the_reparse_is_still_verified_exactly(self):
        for token in ('Exn.Exn (HOL_ERR e)',
                      'Feedback.top_function_of e = "-*"',
                      '"bad theory name: matrix_ephemeral"',
                      "Context.restore saved"):
            self.assertIn(token, self.case)

    def test_the_interactive_flag_is_never_set(self):
        # zapCT would delete the constants the fixture relies on.
        for text in (self.support, self.allocation, self.timing):
            self.assertNotIn("Globals.interactive", text)
            self.assertNotIn("interactive :=", text)

    def test_the_support_reads_no_path_or_environment(self):
        for token in ("export_theory", "getEnv", "OS.FileSys", "FileSys.",
                      "OS.Process", "Posix.", "TextIO.openIn",
                      "TextIO.openOut", "BinIO.open", "Paired.env",
                      "Portable.pwd"):
            with self.subTest(token):
                self.assertNotIn(token, self.support)

    def test_nor_do_the_functions_the_case_calls_into(self):
        # The case calls Theory.link_parents (through the hook's default
        # and the restore) and testutils.runtac; they are the bodies the
        # support's own text cannot vouch for.
        root = a.HERE.parents[3]
        theory = code((root / "src/postkernel/Theory.sml").read_text())
        start = theory.index("fun link_parents thy plist")
        link = theory[start:theory.index("fun incorporate_types", start)]
        utils = code((root / "src/parse/testutils.sml").read_text())
        start = utils.index("fun runtac tac g")
        runtac = utils[start:utils.index("\n", start)]
        self.assertIn("Context.snapshot", runtac)
        for name, body in (("link_parents", link), ("runtac", runtac)):
            for token in ("export_theory", "getEnv", "OS.FileSys",
                          "FileSys.", "OS.Process", "Posix.",
                          "TextIO.openIn", "TextIO.openOut", "BinIO.open",
                          "Portable.pwd"):
                with self.subTest(name=name, token=token):
                    self.assertNotIn(token, body)


class Callbacks(unittest.TestCase):
    """The callback counts the fixture asserts for the dproc deletions are
    derived from the deletion code: `-*` filters the net and the dprocs and
    primes no reducer (`addctxt` calls its `addcontext`, a collector) and
    applies no maker (`mk_rewrs`, which only `++` calls)."""

    @classmethod
    def setUpClass(cls):
        root = a.HERE.parents[3] / "src/simp/src"
        cls.simplib = (root / "simpLib.sml").read_text()
        cls.support = (m.HERE / "MatrixSupport.sml").read_text()

    def definition(self, start, stop):
        i = self.simplib.index(start)
        return self.simplib[i:self.simplib.index(stop, i)]

    def test_the_deletion_calls_no_collector_or_maker(self):
        delete = self.definition("fun (ss as SS{mk_rewrs,history,initial_net",
                                 "fun remove_simps")
        filters = self.definition("fun filter_net_by_names",
                                  "fun (ss as SS{mk_rewrs")
        for body in (delete, filters):
            for token in ("addctxt", "addcontext", "build_from_history",
                          "++", "add_weakener"):
                with self.subTest(token):
                    self.assertNotIn(token, body)
            self.assertIsNone(re.search(r"mk_rewrs\s*[a-z(]", body))
        self.assertIn("filter_net_by_names nms initial_net", delete)
        self.assertIn("filter_dprocs_by_names nms dprocs", delete)

    def test_the_replay_primes_the_existing_dprocs_once_per_addition(self):
        # What history_collectors counts (callbacks n 1): the one existing
        # reducer is primed by the one `++` that adds rewrites to it.
        added = self.definition("val new_dprocs = map (Traverse.addctxt",
                                "val reltravs")
        self.assertIn("Traverse.addctxt (map #2 rewrs)) dprocs'", added)

    def test_both_dproc_deletions_assert_no_callback(self):
        start = self.support.index("fun dproc mixed = let")
        end = self.support.index("in case label of", start)
        body = self.support[start:end]
        self.assertEqual(body.count("callbacks 0 0 (sswork (fn () => "
                                    "from -* pats) verify)"), 1)
        self.assertIn('"exclude_dproc" => dproc false', self.support)
        self.assertIn('"exclude_mixed" => dproc true', self.support)

    def test_the_dproc_fragment_precedes_the_data_it_could_replay(self):
        # A rebuild of the history would run the maker and prime the
        # dprocs only if they are added before the data: the zero counts
        # then mean the deletion replayed nothing.
        start = self.support.index("fun dproc mixed = let")
        body = self.support[start:self.support.index("in case label of",
                                                     start)]
        self.assertIn("val f = setup (SOME maker) ds", body)
        self.assertIn("empty_ss ++ f ++ (if mixed then data else "
                      "empty_ssfrag)", body)

    def test_the_callback_wrapper_checks_both_counters_exactly(self):
        self.assertIn("!makerCalls - !oldM = count * makers andalso",
                      self.support)
        self.assertIn("!collectorCalls - !oldC = count * collectors",
                      self.support)


if __name__ == "__main__":
    unittest.main()
