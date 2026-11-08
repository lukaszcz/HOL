#!/usr/bin/env python3
"""No class of a performance or compatibility test file defines a method
name twice: Python keeps the last, and the earlier copy silently never runs."""
import ast
from pathlib import Path
import unittest

HERE = Path(__file__).resolve().parent


def duplicates(source):
    found = []
    for node in ast.walk(ast.parse(source)):
        if isinstance(node, ast.ClassDef):
            names = [n.name for n in node.body if isinstance(
                n, (ast.FunctionDef, ast.AsyncFunctionDef))]
            found += ["%s.%s" % (node.name, n) for n in sorted(set(names))
                      if names.count(n) > 1]
    return found


class UniqueMethods(unittest.TestCase):
    def test_the_check_sees_a_duplicate(self):
        self.assertEqual(duplicates(
            "class A:\n  def f(self): pass\n  def f(self): pass\n"),
            ["A.f"])

    def test_no_test_class_defines_a_method_twice(self):
        files = sorted(HERE.glob("*.py")) + \
            sorted((HERE.parent / "compatibility").glob("*.py"))
        self.assertTrue(files)
        for path in files:
            with self.subTest(file=path.name):
                self.assertEqual(duplicates(path.read_text()), [])


if __name__ == "__main__":
    unittest.main()
