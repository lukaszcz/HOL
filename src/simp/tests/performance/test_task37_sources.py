#!/usr/bin/env python3
"""The TASK37 identity source lists (task37_sources.py) and their place in
the seals: only the identity tables seal them, so filling one voids no
timing pilot or counts file (design decision 19)."""
import unittest

import acceptance as a
import import_closure as ic
import task31_cases
import task31_identity_grid as idg
import task37_cases as cases
import task37_followup as followup
import task37_grid as grid
import task37_identity as ident
import task37_sources as lists


class Lists(unittest.TestCase):
    def test_the_lists_are_tuples_of_distinct_paths(self):
        for sources in (lists.CLIENT, lists.MATRIX, lists.DOWNSTREAM):
            self.assertIsInstance(sources, tuple)
            self.assertEqual(len(set(sources)), len(sources))

    def test_the_client_list_is_the_closure_task31_identity_used(self):
        """TASK31's identity grid reads `cases.SOURCES` of task31_cases,
        for the same cells as the client table: the elaborated closure."""
        self.assertEqual(lists.CLIENT, tuple(task31_cases.SOURCES))
        self.assertEqual(lists.CLIENT, tuple(sorted(
            set(task31_cases.ELABORATED))))
        self.assertIs(idg.cases, task31_cases)
        self.assertEqual(ident.tables()["client"].cells(),
                         [(c, n) for c, n in idg.every()])

    def test_the_tables_take_their_lists_from_this_module(self):
        found = ident.tables()
        self.assertEqual(found["client"].sources, lists.CLIENT)
        self.assertEqual(found["matrix"].sources, lists.MATRIX)
        self.assertEqual(found["downstream"].sources, lists.DOWNSTREAM)
        for key, constant in (("client", "CLIENT"), ("matrix", "MATRIX"),
                              ("downstream", "DOWNSTREAM")):
            self.assertEqual(found[key].constant, constant)
            self.assertTrue(hasattr(lists, constant))

    def test_the_boundary_lists_of_the_timing_tables_are_not_these(self):
        for t in grid.TABLES.values():
            self.assertIn(t.sources, (cases.MATRIX_TIMING_SOURCES,
                                      cases.CLIENT_TIMING_SOURCES))

    def test_the_procedure_is_documented(self):
        for part in ("--only", "sources --output DIR", "alone",
                     "before the full"):
            self.assertIn(part, lists.__doc__)


class Seals(unittest.TestCase):
    def test_only_identity_seals_the_lists(self):
        name = "task37_sources.py"
        self.assertIn(name, ident.IDENTITY_CODE)
        self.assertTrue((a.HERE / name).is_file())
        for key, sealed in grid.SEALED.items():
            self.assertNotIn(name, sealed, key)
        for key, sealed in followup.SEALED.items():
            self.assertNotIn(name, sealed, key)
        for t in grid.TABLES.values():
            self.assertNotIn(name, t.sealed, t.name)

    def test_no_timing_module_imports_the_lists(self):
        sources = ic.sources()
        timing = ("task37_grid", "task37_followup", "task37_cases")
        for name in timing:
            self.assertNotIn("task37_sources", {
                e[1] for e in ic.edges(sources, name)}, name)
        found, _ = ic.closure(sources, timing)
        self.assertNotIn("task37_sources", found)

    def test_the_identity_module_imports_them(self):
        edges = ic.edges(ic.sources(), "task37_identity")
        self.assertIn(("task37_identity", "task37_sources", None), edges)


if __name__ == "__main__":
    unittest.main()
