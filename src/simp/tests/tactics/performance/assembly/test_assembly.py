"""Offline checks of selected roots and fail-closed collector promotion."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "task18_codegen", Path(__file__).with_name("run_assembly.py"))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class AdapterTests(unittest.TestCase):
    def test_selection(self):
        for name in module.ROOTS + module.HELPERS:
            self.assertTrue(module.core.selected("simpLib." + name + "(2)"))
        self.assertFalse(module.core.selected("simpLib.remove_ssfrags(2)"))

    def test_backend_tree_selection(self):
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            private = Path(tmp)
            body = "LAMBDA(\n <top level>\n BLOCK(\n" + "\n".join(
                " LAMBDA( simpLib." + root + "(1) ARGS=G )"
                for root in module.ROOTS) + "))\n"
            text = ("@@PAIR\t1\tuse\t" + str(private / "simpLib.sml") +
                    "\n" + body + "@@PAIR\t2\tused\t" +
                    str(private / "simpLib.sml") + "\n")
            rows = module.compiler_records(text, private)
            self.assertEqual(rows[0]["kind"], "backend-tree")
            self.assertEqual(rows[0]["text"], body)
            with self.assertRaises(module.paired.InvalidRun):
                module.compiler_records(text.replace(
                    "simpLib.process_tags", "unselected"), private)

    def test_no_promotion_of_fixture_failure(self):
        self.assertFalse(module.core.collection_accepted(dict(
            collection_validated=False, success=False,
            failure="fixture failed")))


if __name__ == "__main__":
    unittest.main()
