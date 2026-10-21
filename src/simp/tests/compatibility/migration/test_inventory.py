"""Fail-closed controls for the inventory, not simplifier semantic tests."""
import csv
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import inventory as inv


class InventoryTests(unittest.TestCase):
    def test_nested_comments_do_not_add_exports(self):
        text = "(* val ghost : int (* type nested *) *) val real : int"
        self.assertEqual(inv.declarations(text), {("val", "real")})

    def test_datatype_constructors_and_record_names(self):
        text = """datatype reducer = REDUCER of {initial: exn}
                  | CONFIG_REDUCER of cfg
                  val reducer_config_data : reducer -> cfg
                  type cfg = {name: string}
                  datatype traversal_policy = ParentFirst | ChildFirst of cfg
end"""
        self.assertEqual(inv.declarations(text), {
            ("datatype", "reducer"), ("constructor", "REDUCER"),
            ("constructor", "CONFIG_REDUCER"), ("val", "reducer_config_data"),
            ("type", "cfg"), ("datatype", "traversal_policy"),
            ("constructor", "ParentFirst"), ("constructor", "ChildFirst"),
        })

    def test_actual_signature_inventory(self):
        delta = inv.validate_signatures(inv.catalog())
        changed = [v for v in delta.values() if v["baseline_exists"]]
        new = [v for v in delta.values() if not v["baseline_exists"]]
        self.assertEqual((len(changed), len(new)), (7, 3))  # congLib unchanged
        self.assertEqual(sum(k == "val" for v in changed
                             for k, _ in v["added"]), 68)
        self.assertEqual(sum(k == "type" for v in changed
                             for k, _ in v["added"]), 11)
        self.assertEqual(sum(k == "val" for v in new
                             for k, _ in v["added"]), 31)

    def test_missing_api_is_rejected(self):
        rows = [r for r in inv.catalog()
                if not (r[1] == "simpLib" and r[3] == "set_term_ord")]
        with self.assertRaisesRegex(ValueError, "uncatalogued signature delta"):
            inv.validate_signatures(rows)

    def test_invented_api_is_rejected(self):
        rows = inv.catalog() + [("T1", "Traverse", "val", "pretend_promote")]
        with self.assertRaisesRegex(ValueError, "uncatalogued signature delta"):
            inv.validate_signatures(rows)

    def test_unknown_signature_is_rejected(self):
        original = inv.git

        def altered(root, *args):
            result = original(root, *args)
            if args[:2] == ("diff", "--name-only"):
                result += b"src/simp/src/Uninventoried.sig\n"
            return result

        with patch.object(inv, "git", side_effect=altered):
            with self.assertRaisesRegex(ValueError, "Unclassified"):
                inv.validate_signatures(inv.catalog())

    def test_every_family_has_table_and_owner(self):
        doc = (inv.HERE / "MIGRATION.md").read_text()
        for group, _, _, _ in inv.catalog():
            self.assertIn("| " + group + ":", doc)
            self.assertTrue(inv.OWNERS[group])
            self.assertTrue(all(8 <= int(n) <= 27
                                for n in inv.OWNERS[group].split(",")))

    def test_every_reference_has_exact_anchor_and_owner(self):
        manifest = json.loads((inv.HERE / "manifest.json").read_text())
        roots = {"repository": inv.ROOT,
                 "external": Path(manifest["external"]["path"])}
        rows = csv.DictReader(io.StringIO(
            (inv.HERE / "references.tsv").read_text()), delimiter="\t")
        sources = {}
        count = 0
        for row in rows:
            scope, path = row["scope"], row["path"]
            key = scope, path
            if key not in sources:
                data = (roots[scope] / path).read_bytes()
                self.assertEqual(inv.digest(data),
                                 manifest["matched_source_sha256"][scope][path])
                sources[key] = data.decode("utf-8", errors="replace").splitlines()
            line = sources[key][int(row["line"]) - 1]
            self.assertIn(row["api"].split(".")[-1], line)
            self.assertIn(row["group"], inv.OWNERS)
            self.assertTrue(row["owners"])
            self.assertTrue(row["category"])
            count += 1
        self.assertEqual(count, sum(s["reference_rows"]
                                    for s in manifest["scans"].values()))

    def test_scanner_keeps_bare_names_but_filters_common_constructors(self):
        with tempfile.TemporaryDirectory(prefix="task07-inventory-") as temp:
            root = Path(temp)
            (root / "test.sml").write_text(
                "val x = rewrite_source_handles ss\n"
                "val y = unrelated.Add\n"
                "val z = SplitData.Add\n")
            rows = [("V1", "simpLib", "val", "rewrite_source_handles"),
                    ("I1", "SplitData", "constructor", "Add")]
            with patch.object(inv, "git", return_value=b"test.sml\0"):
                refs, _, _, count = inv.scan(root, "repository", rows)
            self.assertEqual(count, 1)
            self.assertEqual([r[2] for r in refs], ["1", "3"])
            self.assertTrue(all(r[6] for r in refs))


if __name__ == "__main__":
    unittest.main()
