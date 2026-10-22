"""Pure protocol mutation controls. No HOL, build, or benchmark subprocesses."""
import copy
import sys
import unittest

sys.dont_write_bytecode = True
import run_routes as routes


def events():
    return [[*row[:2], ("Simplification set fragment: fixture\\nRewrite rules:"
                       if row[2] is None else row[2])]
            for row in routes.schema()]


def protocol(rows):
    return "".join("@@PAIR\t" + str(i) + "\t" + "\t".join(row) + "\n"
                   for i, row in enumerate(rows))


class RoutesProtocol(unittest.TestCase):
    def rejected(self, rows):
        with self.assertRaises(routes.paired.InvalidRun):
            routes.behavior(protocol(rows))

    def test_complete_contract(self):
        rows = events()
        self.assertEqual(routes.behavior(protocol(rows)), rows)
        routes.same_behavior(rows, copy.deepcopy(rows))

    def test_missing_duplicate_extra_reordered(self):
        rows = events()
        self.rejected(rows[:-1])
        self.rejected(rows + [rows[-1]])
        self.rejected(rows[:4] + rows[5:])
        rows[0], rows[1] = rows[1], rows[0]
        self.rejected(rows)

    def test_all_fixed_results_fail_closed(self):
        for i, row in enumerate(routes.schema()):
            if row[2] is not None:
                with self.subTest(row=row[:2]):
                    rows = events()
                    rows[i][2] += "WRONG"
                    self.rejected(rows)

    def test_empty_or_unescaped_rendering_rejected(self):
        for value in ("", "not a rendering", "Simplification set fragment: x"):
            rows = events()
            rows[0][2] = value
            self.rejected(rows)

    def test_exact_printer_bytes_not_just_checks(self):
        original = events()
        for suffix in (" ", "\\n", "[lost hypothesis]", "different order"):
            changed = copy.deepcopy(original)
            changed[0][2] += suffix
            # Schema alone cannot know old printer bytes. Pair equality must.
            routes.behavior(protocol(changed))
            with self.assertRaises(routes.paired.InvalidRun):
                routes.same_behavior(original, changed)

    def test_exception_not_allowed(self):
        rows = events()
        rows.insert(8, ["exception", "Option", "Option"])
        self.rejected(rows)

    def test_truncated_and_unordered_protocol(self):
        text = protocol(events())
        with self.assertRaises(routes.paired.InvalidRun):
            routes.behavior(text[:-1])
        with self.assertRaises(routes.paired.InvalidRun):
            routes.behavior(text.replace("@@PAIR\t1\t", "@@PAIR\t9\t", 1))


if __name__ == "__main__":
    unittest.main()
