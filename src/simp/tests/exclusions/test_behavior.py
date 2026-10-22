"""Fail-closed protocol controls for the paired exclusion/replay fixture."""
import copy
import unittest
import run_behavior as runner


def text(rows):
    return ''.join('@@PAIR\t' + str(i) + '\t' + '\t'.join(row) + '\n'
                   for i, row in enumerate(rows))


class BehaviorTests(unittest.TestCase):
    def test_complete(self):
        rows = runner.schema()
        self.assertEqual(len([r for r in rows if r[0] == 'check']), 42)
        self.assertEqual(runner.behavior(text(rows)), rows)

    def test_missing_check(self):
        with self.assertRaises(Exception):
            runner.behavior(text(runner.schema()[1:]))

    def test_callback_order(self):
        rows = copy.deepcopy(runner.schema())
        rows[4][2] = 'd1:a;m1:a;weak:;m1:b;m2:b;weak:b'
        with self.assertRaises(Exception):
            runner.behavior(text(rows))

    def test_callback_count(self):
        rows = copy.deepcopy(runner.schema())
        rows[4][2] += ';weak:'
        with self.assertRaises(Exception):
            runner.behavior(text(rows))

    def test_wrong_proof(self):
        rows = copy.deepcopy(runner.schema())
        rows[0][2] = 'fail'
        with self.assertRaises(Exception):
            runner.behavior(text(rows))

    def test_reordered_checks(self):
        rows = runner.schema()
        rows[0], rows[1] = rows[1], rows[0]
        with self.assertRaises(Exception):
            runner.behavior(text(rows))

    def test_missing_completion(self):
        with self.assertRaises(Exception):
            runner.behavior(text(runner.schema()[:-1]))

    def test_cross_version_difference(self):
        rows = runner.schema()
        with self.assertRaises(Exception):
            runner.same_behavior(rows, rows[:-1])


if __name__ == '__main__':
    unittest.main()
