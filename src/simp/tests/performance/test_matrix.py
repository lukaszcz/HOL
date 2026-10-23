#!/usr/bin/env python3
"""Fail-closed P09 coverage/fixture controls, not performance measurements."""
from contextlib import redirect_stderr, redirect_stdout
import copy
import io
import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

import matrix_schema as schema


class MatrixTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = schema.load_matrix()

    def setUp(self):
        self.data = copy.deepcopy(self.original)

    def validate(self):
        return schema.validate_matrix(self.data)

    def test_frozen_inventory(self):
        self.assertEqual(len(schema.REQUIRED_REQUIREMENTS), 69)
        self.assertEqual(len(self.original["requirements"]), 69)
        self.assertEqual(len(self.original["cases"]), 107)
        self.assertEqual(len(schema.MATRIX_CASES), 51)
        self.assertEqual(schema.REQUIRED_COVERAGE["exclusions.marker_routes"],
                         ("exclude_marker", "exclude_marker_reuse",
                          "exclude_tactic_construct", "exclude_tactic_reuse",
                          "exclude_tactic_complete"))
        self.assertEqual(schema.REQUIRED_COVERAGE["history.custom_collectors"],
                         ("history_collectors", "compile_collector",
                          "history_makers"))
        self.assertEqual(set(self.original["requirements"]),
                         schema.REQUIRED_REQUIREMENTS)
        self.assertEqual(self.validate(), self.data)
        self.assertEqual({key.split(".")[0]
                          for key in schema.REQUIRED_REQUIREMENTS},
                         {"fragments", "compilation", "exclusions", "history",
                          "traversal", "tactics", "loading", "storage",
                          "downstream", "protocol"})

    def test_every_requirement_deletion_fails_even_when_cases_shared(self):
        for key in self.original["requirements"]:
            with self.subTest(key=key):
                self.data = copy.deepcopy(self.original)
                del self.data["requirements"][key]
                with self.assertRaisesRegex(ValueError, "requirements"):
                    self.validate()

    def test_every_case_deletion_fails(self):
        for key in self.original["cases"]:
            with self.subTest(key=key):
                self.data = copy.deepcopy(self.original)
                del self.data["cases"][key]
                with self.assertRaisesRegex(ValueError, "cases"):
                    self.validate()

    def test_unreferenced_extra_case_rejected(self):
        self.data["cases"]["unreferenced"] = {
            "fixture": "ClientPerformance.sml", "sizes": "singleton"}
        with self.assertRaises(ValueError):
            self.validate()

    def test_required_rows_not_replaceable_by_unrelated_cases(self):
        for key in schema.REQUIRED_COVERAGE:
            with self.subTest(key=key):
                self.data = copy.deepcopy(self.original)
                self.data["requirements"][key]["cases"] = ["storage_graph"]
                if schema.REQUIRED_COVERAGE[key] == ("storage_graph",):
                    self.data["requirements"][key]["cases"] = ["frag_create"]
                with self.assertRaisesRegex(ValueError, "coverage"):
                    self.validate()

    def test_all_case_lists_reject_duplicates(self):
        for key in schema.REQUIRED_COVERAGE:
            with self.subTest(key=key):
                self.data = copy.deepcopy(self.original)
                row = self.data["requirements"][key]["cases"]
                row.append(row[0])
                with self.assertRaisesRegex(ValueError, "duplicate"):
                    self.validate()

    def test_unknown_requirement_and_typo_rejected(self):
        for key in ("fragments.creatoin", "new.gate"):
            with self.subTest(key=key):
                self.data = copy.deepcopy(self.original)
                self.data["requirements"][key] = {"cases": ["frag_create"]}
                with self.assertRaisesRegex(ValueError, "requirements"):
                    self.validate()

    def test_absent_and_unknown_fields_every_object_level(self):
        locations = [(), ("protocol",), ("size_sets",), ("cases",),
                     ("cases", "frag_create"), ("requirements",),
                     ("requirements", "fragments.creation"),
                     ("blockers",), ("externals",),
                     ("blockers", "allocation_prerequisite"),
                     ("externals", "loading_audit")]
        for path in locations:
            for extra in (False, True):
                with self.subTest(path=path, extra=extra):
                    self.data = copy.deepcopy(self.original)
                    target = self.data
                    for key in path:
                        target = target[key]
                    if extra:
                        target["typo"] = "bad"
                    else:
                        del target[next(iter(target))]
                    with self.assertRaises(ValueError):
                        self.validate()

    def test_protocol_exact_and_no_bool_int_confusion(self):
        for key in schema.PROTOCOL:
            for value in (None, [], {}, 1, True, "disabled"):
                if type(value) is type(schema.PROTOCOL[key]) and \
                        value == schema.PROTOCOL[key]:
                    continue
                with self.subTest(key=key, value=value):
                    self.data = copy.deepcopy(self.original)
                    self.data["protocol"][key] = value
                    with self.assertRaisesRegex(ValueError, "protocol"):
                        self.validate()
        self.data = copy.deepcopy(self.original)
        self.data["schema"] = True
        with self.assertRaisesRegex(ValueError, "schema"):
            self.validate()

    def test_baseline_scope_version_pinned(self):
        for key in ("schema", "baseline", "scope"):
            with self.subTest(key=key):
                self.data = copy.deepcopy(self.original)
                self.data[key] = "other"
                with self.assertRaises(ValueError):
                    self.validate()

    def test_size_grid_deletions_duplicates_order_types_and_extras(self):
        for key, grid in schema.SIZE_SETS.items():
            for value in ([], grid[:-1], grid + [grid[-1]],
                          list(reversed(grid)) + [5], [True], [1.0],
                          [str(n) for n in grid], grid + [3]):
                with self.subTest(key=key, value=value):
                    self.data = copy.deepcopy(self.original)
                    self.data["size_sets"][key] = value
                    with self.assertRaises(ValueError):
                        self.validate()
        self.data = copy.deepcopy(self.original)
        self.data["size_sets"]["rules"][1] = True
        with self.assertRaisesRegex(ValueError, "grid"):
            self.validate()

    def test_every_case_binding_frozen(self):
        for key in self.original["cases"]:
            for field, value in (("fixture", "../secret.sml"),
                                 ("fixture", "Typo.sml"),
                                 ("sizes", "singleton"), ("sizes", "rule")):
                if value == self.original["cases"][key][field]:
                    continue
                with self.subTest(key=key, field=field, value=value):
                    self.data = copy.deepcopy(self.original)
                    self.data["cases"][key][field] = value
                    with self.assertRaisesRegex(ValueError, "binding"):
                        self.validate()

    def test_all_stages_required(self):
        for key, coverage in schema.REQUIRED_COVERAGE.items():
            if key.startswith("tactics.") or key in (
                    "compilation.stages", "traversal.construction",
                    "exclusions.marker_routes", "history.custom_collectors"):
                for case in coverage:
                    with self.subTest(key=key, case=case):
                        self.data = copy.deepcopy(self.original)
                        self.data["requirements"][key]["cases"].remove(case)
                        with self.assertRaises(ValueError):
                            self.validate()

    def test_requirement_resolution_exactly_one_route(self):
        for key, row in self.original["requirements"].items():
            with self.subTest(key=key):
                self.data = copy.deepcopy(self.original)
                other = "cases" if "cases" not in row else "blocker"
                self.data["requirements"][key][other] = "loading_prerequisite"
                with self.assertRaises(ValueError):
                    self.validate()

    def test_missing_real_blocker_is_not_pass(self):
        for key in self.original["blockers"]:
            with self.subTest(key=key):
                self.data = copy.deepcopy(self.original)
                del self.data["blockers"][key]
                with self.assertRaises(ValueError):
                    self.validate()

    def test_blocker_and_external_records_must_be_substantive(self):
        bad_fields = {
            "reason": (None, "", "   ", "missing receipt"),
            "commands": (None, [], [""], ["echo pass"],
                         ["python3 'unclosed"], ["poly\n--version"],
                         ["poly --version", "poly --version"]),
            "gate_owner": (None, "", "somebody", "TASK99", "TASK29, TASK99"),
            "status": (None, "pass", "inconclusive"),
        }
        for group in ("blockers", "externals"):
            for name in self.original[group]:
                for field, bad_values in bad_fields.items():
                    for value in bad_values:
                        with self.subTest(group=group, name=name,
                                          field=field, value=value):
                            self.data = copy.deepcopy(self.original)
                            self.data[group][name][field] = value
                            with self.assertRaises(ValueError):
                                self.validate()

    def test_unknown_dangling_gate_references(self):
        for key, mode in (("loading.startup_time", "blocker"),
                          ("protocol.extensions_enabled", "external")):
            with self.subTest(key=key):
                self.data = copy.deepcopy(self.original)
                self.data["requirements"][key][mode] = "typo"
                with self.assertRaises(ValueError):
                    self.validate()
        for group in ("blockers", "externals"):
            self.data = copy.deepcopy(self.original)
            self.data[group]["unreferenced"] = copy.deepcopy(
                next(iter(self.data[group].values())))
            with self.assertRaises(ValueError):
                self.validate()

    def test_runnable_checks_not_relabelled_missing_receipt_blockers(self):
        for key in schema.REQUIRED_EXTERNALS:
            with self.subTest(key=key):
                self.data = copy.deepcopy(self.original)
                self.data["requirements"][key] = {
                    "blocker": "loading_prerequisite"}
                with self.assertRaises(ValueError):
                    self.validate()

    def test_extension_and_load_commands_mandatory_not_dry_runs(self):
        for name, commands in schema.EXTERNAL_COMMANDS.items():
            for i in range(len(commands)):
                for value in (commands[:i] + commands[i+1:],
                              commands[:i] + [commands[i] + " -n"] +
                              commands[i+1:]):
                    with self.subTest(name=name, i=i, value=value):
                        self.data = copy.deepcopy(self.original)
                        self.data["externals"][name]["commands"] = value
                        with self.assertRaises(ValueError):
                            self.validate()

    def test_get_case_all_legal_sizes(self):
        # Avoid disk JSON rereads here, but every call still validates sources.
        for name, row in self.original["cases"].items():
            for size in self.original["size_sets"][row["sizes"]]:
                with self.subTest(case=name, size=size):
                    self.assertEqual(schema.get_case(
                        name, size, matrix=self.data), row["fixture"])

    def test_get_case_rejects_sizes_per_case_not_union(self):
        for case in ("traversal_deep", "traversal_construct",
                     "downstream_arithmetic", "frag_create"):
            for size in (3, -1, 10001, True, False, 1.0, "1", None):
                with self.subTest(case=case, size=size):
                    with self.assertRaisesRegex(ValueError, "size"):
                        schema.get_case(case, size, matrix=self.data)
        with self.assertRaises(ValueError):
            schema.get_case("traversal_deep", 1000, matrix=self.data)
        with self.assertRaises(ValueError):
            schema.get_case("traversal_construct", 1, matrix=self.data)
        with self.assertRaises(ValueError):
            schema.get_case("downstream_arithmetic", 0, matrix=self.data)

    def test_get_case_unknown_and_malformed_case(self):
        for name in ("frag_creat", "../case", "FRAG_CREATE", "", None, [], 1):
            with self.subTest(case=name), self.assertRaises(ValueError):
                schema.get_case(name, 0, matrix=self.data)

    def test_get_case_revalidates_explicit_matrix(self):
        del self.data["requirements"]["fragments.creation"]
        with self.assertRaises(ValueError):
            schema.get_case("frag_create", 0, matrix=self.data)

    def test_get_case_default_returns_basename(self):
        self.assertEqual(schema.get_case("frag_create", 0),
                         "MatrixPerformance.sml")
        self.assertEqual(schema.get_case("tactic_reqd_reuse", 1000),
                         "ClientPerformance.sml")

    def test_report_all_gates_distinguishes_readiness_not_acceptance(self):
        report = schema.report(self.data)
        self.assertTrue(report["schema_valid"])
        self.assertFalse(report["performance_acceptance"])
        self.assertEqual(report["counts"], {
            "runnable_case": 53, "runnable_external": 9,
            "prerequisite_blocked": 7})
        self.assertEqual(set(report["gates"]), schema.REQUIRED_REQUIREMENTS)
        for name, row in report["gates"].items():
            with self.subTest(name=name):
                self.assertNotIn(row["status"], ("pass", "inconclusive"))
                if row["status"] == "runnable_case":
                    self.assertTrue(row["workloads"])
                    for case in row["workloads"]:
                        self.assertTrue(case["sizes"])
                        self.assertIn(case["case"], case["command_template"])
                else:
                    self.assertTrue(row["commands"])
                    self.assertTrue(row["reason"])
                    self.assertTrue(row["gate_owner"].startswith("TASK"))
        self.assertEqual(report["gates"]["loading.fresh_simpLib"]["status"],
                         "runnable_external")
        self.assertEqual(report["gates"]["loading.startup_time"]["status"],
                         "runnable_external")

    def test_report_refuses_invalid_matrix(self):
        del self.data["requirements"]["storage.gc_time"]
        with self.assertRaises(ValueError):
            schema.report(self.data)


class FileTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="task28-matrix-schema-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for name in ("matrix.json", "MatrixPerformance.sml",
                     "MatrixSupport.sml", "ClientPerformance.sml"):
            shutil.copyfile(schema.HERE / name, self.root / name)
        self.path = self.root / "matrix.json"

    def load(self):
        return schema.load_matrix(self.path)

    def change(self, name, old, new):
        path = self.root / name
        text = path.read_text()
        self.assertIn(old, text)
        path.write_text(text.replace(old, new, 1))

    def test_load_checks_live_fixture_directory(self):
        self.assertEqual(len(self.load()["requirements"]), 69)
        for name in ("MatrixPerformance.sml", "MatrixSupport.sml",
                     "ClientPerformance.sml"):
            with self.subTest(name=name):
                path = self.root / name
                text = path.read_text()
                path.unlink()
                with self.assertRaisesRegex(ValueError, "missing fixture"):
                    self.load()
                path.write_text(text)

    def test_missing_ledger(self):
        self.path.unlink()
        with self.assertRaisesRegex(ValueError, "cannot read"):
            self.load()

    def test_empty_truncated_and_invalid_json(self):
        for text in ("", "{", "[]", "null", "1", "true"):
            with self.subTest(text=text):
                self.path.write_text(text)
                with self.assertRaises(ValueError):
                    self.load()

    def test_duplicate_json_keys_at_every_level(self):
        original = self.path.read_text()
        for old, new in (
                ('"schema": 1,', '"schema": 1, "schema": 1,'),
                ('"selector": "PERF_CASE",',
                 '"selector": "PERF_CASE", "selector": "PERF_CASE",'),
                ('"fixture": "MatrixPerformance.sml",',
                 '"fixture": "MatrixPerformance.sml", "fixture": "x",'),
                ('"cases": ["frag_create"]',
                 '"cases": ["frag_create"], "cases": ["frag_create"]'),
                ('"status": "blocked",',
                 '"status": "blocked", "status": "blocked",')):
            with self.subTest(old=old):
                self.assertIn(old, original)
                self.path.write_text(original.replace(old, new, 1))
                with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                    self.load()

    def test_nonfinite_json_rejected(self):
        original = self.path.read_text()
        for value in ("NaN", "Infinity", "-Infinity"):
            with self.subTest(value=value):
                self.path.write_text(original.replace('"schema": 1',
                                                      '"schema": ' + value))
                with self.assertRaisesRegex(ValueError, "nonfinite"):
                    self.load()

    def test_entry_fixture_cannot_be_empty_or_stop_dispatching(self):
        path = self.root / "MatrixPerformance.sml"
        original = path.read_text()
        changed = original.replace("workload label size", "workload x y")
        for text in ("", changed):
            with self.subTest(empty=not text):
                path.write_text(text)
                with self.assertRaisesRegex(ValueError, "selection dispatch"):
                    self.load()

    def test_matrix_source_list_typo(self):
        self.change("MatrixSupport.sml", '"frag_create",', '"frag_creat",')
        with self.assertRaisesRegex(ValueError, "cases does not match"):
            self.load()

    def test_matrix_source_duplicate(self):
        self.change("MatrixSupport.sml", '"frag_create",',
                    '"frag_create", "frag_create",')
        with self.assertRaisesRegex(ValueError, "duplicate"):
            self.load()

    def test_matrix_source_dispatch_deleted_or_typo(self):
        self.change("MatrixSupport.sml", '"frag_create" =>',
                    '"frag_typo" =>')
        with self.assertRaisesRegex(ValueError, "dispatch"):
            self.load()

    def test_matrix_source_grid_changed(self):
        self.change("MatrixSupport.sml", "val sizes = [0,1,10,100,1000,10000]",
                    "val sizes = [0,1,10,100,1000]")
        with self.assertRaisesRegex(ValueError, "sizes"):
            self.load()

    def test_client_source_atomic_case_changed(self):
        self.change("ClientPerformance.sml", '"traversal_construct" =>',
                    '"traversal_typo" =>')
        with self.assertRaisesRegex(ValueError, "source cases"):
            self.load()

    def test_client_source_downstream_case_deleted(self):
        self.change("ClientPerformance.sml", '"downstream_reduce" =>',
                    '"not_a_client_case" =>')
        with self.assertRaisesRegex(ValueError, "source cases"):
            self.load()

    def test_client_source_family_missing(self):
        self.change("ClientPerformance.sml",
                    '["supplied","installed","asm","full"',
                    '["supplied","installed","full"')
        with self.assertRaisesRegex(ValueError, "family inventory"):
            self.load()

    def test_client_source_stage_missing(self):
        self.change("ClientPerformance.sml",
                    '["construct","reuse","complete"]',
                    '["construct","reuse"]')
        with self.assertRaisesRegex(ValueError, "stages"):
            self.load()

    def test_client_source_duplicate_family(self):
        self.change("ClientPerformance.sml",
                    '["supplied","installed","asm","full"',
                    '["supplied","installed","asm","supplied","full"')
        with self.assertRaisesRegex(ValueError, "duplicate"):
            self.load()

    def test_source_cannot_hide_real_case_in_comment(self):
        self.change("ClientPerformance.sml", '"traversal_construct" =>',
                    '(* "traversal_construct" => *) "typo" =>')
        with self.assertRaisesRegex(ValueError, "source cases"):
            self.load()

    def test_comments_and_nested_comments_not_fake_case_inventories(self):
        path = self.root / "MatrixSupport.sml"
        path.write_text('(* val cases = ["typo"] (* nested *) *)\n' +
                        path.read_text())
        self.assertEqual(len(self.load()["cases"]), 107)

    def test_cli_human_and_json_reports(self):
        for json_mode in (False, True):
            out = io.StringIO()
            args = ["--matrix", str(self.path)]
            if json_mode:
                args.append("--json")
            with redirect_stdout(out):
                self.assertEqual(schema.main(args), 0)
            if json_mode:
                result = json.loads(out.getvalue())
                self.assertFalse(result["performance_acceptance"])
                self.assertEqual(len(result["gates"]), 69)
            else:
                for key in schema.REQUIRED_REQUIREMENTS:
                    self.assertIn(key + ":", out.getvalue())
                self.assertIn("Not performance acceptance", out.getvalue())
                self.assertIn("check-full", out.getvalue())
                self.assertIn("root-wrapper.sh", out.getvalue())

    def test_cli_fail_closed(self):
        self.path.write_text('{"schema": 1}')
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            self.assertEqual(schema.main(["--matrix", str(self.path)]), 1)
        self.assertEqual(out.getvalue(), "")
        self.assertIn("INVALID MATRIX", err.getvalue())

    def test_default_get_case_rereads_ledger(self):
        with patch.object(schema, "HERE", self.root):
            self.assertEqual(schema.get_case("frag_create", 0),
                             "MatrixPerformance.sml")
            data = json.loads(self.path.read_text())
            del data["requirements"]["fragments.creation"]
            self.path.write_text(json.dumps(data))
            with self.assertRaises(ValueError):
                schema.get_case("frag_create", 0)


if __name__ == "__main__":
    unittest.main()
