"""Offline checks on the adapter selection and maintained acceptance gate."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location(
    "task17_codegen", Path(__file__).with_name("run_assembly.py"))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)


class AdapterTests(unittest.TestCase):
    def test_selection(self):
        for name in module.ROOTS + module.HELPERS:
            self.assertTrue(module.core.selected("simpLib." + name + "(2)"))
        self.assertFalse(module.core.selected("simpLib.SIMP_CONV(2)"))

    def test_no_promotion_of_fixture_failure(self):
        self.assertFalse(module.core.collection_accepted(dict(
            collection_validated=False, success=False,
            failure="fixture failed")))


if __name__ == "__main__":
    unittest.main()
