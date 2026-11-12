import copy
import json
import unittest
from pathlib import Path
from unittest.mock import patch

import check_design as design


class DesignTests(unittest.TestCase):
    def setUp(self):
        self.graph = json.loads((design.HERE / "graph.json").read_text())
        self.table = design.TABLE.read_text()

    def test_all_240_api_decisions(self):
        self.assertEqual(design.validate_table(self.table), 240)

    def test_existing_rows_are_develop_exports(self):
        design.validate_existing()
        rows = [dict(group="C2", old_api="congLib.CONGRUENCE_EQ_SIMP_RULE",
                     kind="existing")]
        with self.assertRaisesRegex(ValueError, "not exported by develop"):
            design.validate_existing(rows)
        rows[0]["old_api"] = "noSuchLib.f"
        with self.assertRaisesRegex(ValueError, "no develop signature"):
            design.validate_existing(rows)

    def test_existing_rows_reject_non_exports(self):
        # Names that appear only in a comment, in `signature X = sig`, or
        # not at all must be rejected; a real export must be accepted.
        for api in ["congLib.y", "simpLib.BoundedRewrites", "congLib.sig"]:
            rows = [dict(group="C2", old_api=api, kind="existing")]
            with self.assertRaisesRegex(ValueError, "not exported"):
                design.validate_existing(rows)
        design.validate_existing(
            [dict(group="B1", old_api="simpLib.SF", kind="existing")])

    def test_only_existing_rows_are_checked(self):
        rows = [dict(group="T1", old_api="simpLib.BoundedRewrites",
                     kind="val")]
        design.validate_existing(rows)

    def test_shared_export_needs_row_or_justification(self):
        old, shared = design.read_old_rows(), design.read_shared()
        design.validate_completeness(old, shared)
        self.assertIn("simpLib.Cong", shared)
        # A missing row fails.
        rows = [r for r in old if r["old_api"] != "simpLib.SIMP_TAC"]
        with self.assertRaisesRegex(ValueError, "neither row"):
            design.validate_completeness(rows, shared)
        # An allowlisted name passes without a row.
        self.assertNotIn("simpLib.Cong", {r["old_api"] for r in old})
        # An allowlisted name that also has a row is stale.
        stale = dict(shared, **{"simpLib.SIMP_TAC": "x"})
        with self.assertRaisesRegex(ValueError, "has a row"):
            design.validate_completeness(old, stale)
        # An allowlisted name that is not a shared export is stale.
        for api in ["simpLib.threaded_cong_ss", "simpLib.noSuchName"]:
            with self.assertRaisesRegex(ValueError, "not a shared export"):
                design.validate_completeness(old, dict(shared, **{api: "x"}))
        # Removing a justified entry fails.
        short = {k: v for k, v in shared.items() if k != "simpLib.Cong"}
        with self.assertRaisesRegex(ValueError, "neither row"):
            design.validate_completeness(old, short)

    def test_missing_api_is_not_a_pass(self):
        lines = self.table.splitlines(keepends=True)
        with self.assertRaisesRegex(ValueError, "missing/stale"):
            design.validate_table("".join(lines[:-1]))

    def test_changed_construction_is_not_a_pass(self):
        rows = design.expected_rows()
        rows[0]["construction"] = ""
        with self.assertRaisesRegex(ValueError, "missing/stale"):
            design.validate_table(design.table_text(rows))

    def test_export_must_belong_to_its_prototype_module(self):
        original = Path.read_text
        def missing(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            if path.name == "Task08API.sml":
                text = text.replace(
                    "    val dproc_ss : T.reducer -> ssfrag\n", "")
                text += "\n(* val dproc_ss exists only outside S *)\n"
            return text
        with patch.object(Path, "read_text", missing):
            with self.assertRaisesRegex(ValueError, "missing scoped"):
                design.validate_table(self.table)

    def test_external_rows_require_typed_provider_not_fake_exports(self):
        original = Path.read_text
        def missing(path, *args, **kwargs):
            text = original(path, *args, **kwargs)
            return text.replace("    type provider\n", "")
        with patch.object(Path, "read_text", missing):
            with self.assertRaisesRegex(ValueError, "typed external provider"):
                design.validate_table(self.table)

    def test_final_graph_and_all_cutovers(self):
        order = design.validate_graph(self.graph)
        self.assertEqual(len(order), len(self.graph["nodes"]))
        self.assertLess(order.index("Cond_rewr"),
                        order.index("Cond_rewrExt"))
        self.assertLess(order.index("simpExtLib"), order.index("boolSimpsExt"))

    def test_recipe_cycle_is_rejected(self):
        self.graph["nodes"]["simpExtLib"]["imports"].append("boolSimpsExt")
        with self.assertRaisesRegex(ValueError, "cycle"):
            design.validate_graph(self.graph)

    def test_indirect_ordinary_extension_import_rejected(self):
        self.graph["nodes"]["Trace"]["imports"].append("simpMarkerTheory")
        with self.assertRaisesRegex(ValueError, "reaches extension"):
            design.validate_graph(self.graph)

    def test_unbounded_transition_is_rejected(self):
        for edge in self.graph["transitional_edges"]:
            graph = copy.deepcopy(self.graph)
            graph["transitional_edges"][0]["remove"] = 27
            with self.assertRaisesRegex(ValueError, "unbounded"):
                design.validate_graph(graph)
            self.assertIn(edge["remove"], {12, 13, 16})

    def test_missing_module_availability_is_rejected(self):
        self.graph["introduced_nodes"].pop("Cond_rewrExt")
        with self.assertRaisesRegex(ValueError, "module-availability"):
            design.validate_graph(self.graph)

    def test_missing_transition_is_rejected(self):
        self.graph["transitional_edges"].pop()
        with self.assertRaisesRegex(ValueError, "missing transitional"):
            design.validate_graph(self.graph)

    def test_missing_cutover_is_rejected(self):
        self.graph["cutovers"].remove(14)
        with self.assertRaisesRegex(ValueError, "missing structural"):
            design.validate_graph(self.graph)

    def good_output(self):
        return "\n".join(
            ["TASK08_COMPLETE checks=29"] +
            ["static rejection: " + n + " ..." for n in design.NEGATIVES] +
            ["TASK08_LOADED " + str(design.HERE / n) for n in
             ["Task08API", "Task08TraverseExt", "Task08ReducerTypes",
              "Task08Clients", "Task08Cutovers", "Task08Controls",
              "Task08Reducers"]])

    def test_complete_output_only(self):
        design.validate_output(0, self.good_output())
        for code, output in [(1, self.good_output()), (0, ""),
                             (0, self.good_output() * 2)]:
            with self.assertRaisesRegex(ValueError, "incomplete/failed"):
                design.validate_output(code, output)

    def test_missing_static_case_is_rejected(self):
        text = self.good_output().replace(
            "static rejection: set-to-legacy", "oops")
        with self.assertRaisesRegex(ValueError, "missing static"):
            design.validate_output(0, text)

    def test_stale_module_path_is_rejected(self):
        text = self.good_output().replace(str(design.HERE), "/stale")
        with self.assertRaisesRegex(ValueError, "private module"):
            design.validate_output(0, text)


if __name__ == "__main__":
    unittest.main()
